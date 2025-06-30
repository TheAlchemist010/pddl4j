/*
 * Copyright (c) 2020 by Damien Pellier <Damien.Pellier@imag.fr>.
 *
 * This file is part of PDDL4J library.
 *
 * PDDL4J is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.
 *
 * PDDL4J is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty
 * of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License along with PDDL4J.
 * If not, see <http://www.gnu.org/licenses/>
 */

package fr.uga.pddl4j.problem;

import fr.uga.pddl4j.problem.operator.Condition;
import fr.uga.pddl4j.parser.ParsedProblem;
import fr.uga.pddl4j.problem.DefaultProblem;
import fr.uga.pddl4j.parser.Expression;
import fr.uga.pddl4j.problem.operator.Effect;
import fr.uga.pddl4j.problem.operator.ConditionalEffect;
import fr.uga.pddl4j.problem.operator.Action;
import fr.uga.pddl4j.problem.operator.Constants;
import fr.uga.pddl4j.parser.Symbol;
import fr.uga.pddl4j.parser.UnexpectedExpressionException;
import fr.uga.pddl4j.parser.SymbolType;
import fr.uga.pddl4j.parser.Connector;
import fr.uga.pddl4j.parser.TypedSymbol;



import java.util.List;
import java.util.ArrayList;




/**
 * This class implements a goal, i.e., a set of positives and negative fluents.
 *
 * @author D. Pellier
 * @version 1.0 - 28.04.2020
 * @since 4.0
 */
public class Goal extends Condition {

    /**
     * Create a new goal from a other goal.
     *
     * @param goal the other goal.
     */
    public Goal(Goal goal) {
        super(goal);
    }

    /**
     *  Create a new goal from a other goal.
     *
     * @param condition the other goal.
     */
    public Goal(Condition condition) {
        super(condition);
    }

    /**
     *  Create a new empty goal from a other goal.
     */
    public Goal() {
        super();
    }

    /**
     *  Create a new goal from an existing problem and a goal expression 
     */

    public static Goal GoalFromExistingProblem(DefaultProblem coreProblem, Expression<String> goalExpression) {
        Expression<Integer> intGoal = initExpression(goalExpression, new ArrayList<>(), coreProblem);
        return finalizeGoal(intGoal, coreProblem);
    }

    /**
     * Encodes an specified expression into its integer representation.
     *
     * <p>Notes:
     * <ul>
     * <li>equal predicate used specified value of -1.</li>
     * <li>variables used negative values in [-1,-infinity[.</li>
     * </ul>
     *
     * @param exp       the expression to encode.
     * @param variables the list of variable already encoded.
     * @return the integer representation of the specified expression.
     */
    protected static Expression<Integer> initExpression(final Expression<String> exp,
                                           final List<String> variables,
                                           DefaultProblem coreProblem) {
        final Expression<Integer> intExp = new Expression<>(exp.getConnector());
        switch (exp.getConnector()) {
            case EQUAL_ATOM:
                List<Symbol<Integer>> args = new ArrayList<>(exp.getArguments().size());
                for (int i = 0; i < exp.getArguments().size(); i++) {
                    final Symbol<String> argument = exp.getArguments().get(i);
                    if (argument.getType().equals(SymbolType.VARIABLE)) {
                        args.add(new Symbol<>(SymbolType.VARIABLE, -variables.indexOf(argument.getValue()) - 1));
                    } else {
                        args.add(new Symbol<>(SymbolType.CONSTANT,
                            coreProblem.getConstantSymbols().indexOf(argument.getValue())));
                    }
                }
                intExp.setArguments(args);
                break;
            case FN_HEAD:
                final String functor = exp.getSymbol().getValue();
                intExp.setSymbol(new Symbol<Integer>(SymbolType.FUNCTOR, coreProblem.getFunctions().indexOf(functor)));
                args = new ArrayList<>(exp.getArguments().size());
                for (int i = 0; i < exp.getArguments().size(); i++) {
                    final Symbol<String> argument = exp.getArguments().get(i);
                    if (argument.getType().equals(SymbolType.VARIABLE)) {
                        args.add(new Symbol<>(SymbolType.VARIABLE, -variables.indexOf(argument.getValue()) - 1));
                    } else {
                        args.add(new Symbol<>(SymbolType.CONSTANT,
                            coreProblem.getConstantSymbols().indexOf(argument.getValue())));
                    }
                }
                intExp.setArguments(args);
                break;
            case ATOM:
                final String predicate = exp.getSymbol().getValue();
                intExp.setSymbol(new Symbol<>(SymbolType.PREDICATE, coreProblem.getPredicateSymbols().indexOf(predicate)));
                args = new ArrayList<>(exp.getArguments().size());
                for (int i = 0; i < exp.getArguments().size(); i++) {
                    final Symbol<String> argument = exp.getArguments().get(i);
                    if (argument.getType().equals(SymbolType.VARIABLE)) {
                        args.add(new Symbol<>(SymbolType.VARIABLE, -variables.indexOf(argument.getValue()) - 1));
                    } else {
                        args.add(new Symbol<>(SymbolType.CONSTANT,
                            coreProblem.getConstantSymbols().indexOf(argument.getValue())));
                    }
                }
                intExp.setArguments(args);
                break;
            case AND:
            case OR:
                for (int i = 0; i < exp.getChildren().size(); i++) {
                    intExp.getChildren().add(initExpression(exp.getChildren().get(i), variables, coreProblem));
                }
                break;
            case FORALL:
            case EXISTS:
                final List<String> newVariables = new ArrayList<>(variables);
                final List<TypedSymbol<String>> qvar = exp.getQuantifiedVariables();
                final String type = toStringType(qvar.get(0).getTypes());
                int typeIndex = coreProblem.getTypes().indexOf(type);
                final TypedSymbol<Integer> intQvar  = new TypedSymbol<Integer>(SymbolType.VARIABLE,
                    -variables.size() - 1);
                intQvar.addType(new Symbol<>(SymbolType.TYPE, typeIndex));
                intExp.addQuantifiedVariable(intQvar);
                newVariables.add(qvar.get(0).getValue());
                if (qvar.size() == 1) {
                    intExp.getChildren().add(initExpression(exp.getChildren().get(0), newVariables, coreProblem));
                } else {
                    qvar.remove(0);
                    intExp.getChildren().add(initExpression(exp, newVariables, coreProblem));
                }
                break;
            case FN_ATOM:
            case WHEN:
            case TIMED_LITERAL:
            case LESS_COMPARISON:
            case LESS_OR_EQUAL_COMPARISON:
            case EQUAL_COMPARISON:
            case GREATER_COMPARISON:
            case GREATER_OR_EQUAL_COMPARISON:
            case ASSIGN:
            case INCREASE:
            case DECREASE:
            case SCALE_UP:
            case SCALE_DOWN:
            case MULTIPLICATION:
            case DIVISION:
            case MINUS:
            case PLUS:
            case SOMETIME_AFTER_CONSTRAINT:
            case SOMETIME_BEFORE_CONSTRAINT:
            case WITHIN_CONSTRAINT:
            case HOLD_AFTER_CONSTRAINT:
                intExp.getChildren().add(initExpression(exp.getChildren().get(0), variables, coreProblem));
                intExp.getChildren().add(initExpression(exp.getChildren().get(1), variables, coreProblem));
                break;
            case AT_START:
            case AT_END:
            case MINIMIZE:
            case MAXIMIZE:
            case UMINUS:
            case NOT:
            case ALWAYS_CONSTRAINT:
            case OVER_ALL:
            case SOMETIME_CONSTRAINT:
            case AT_MOST_ONCE_CONSTRAINT:
            case F_EXP:
            case F_EXP_T:
                intExp.getChildren().add(initExpression(exp.getChildren().get(0), variables, coreProblem));
                break;
            case NUMBER:
                intExp.setValue(exp.getValue());
                break;
            case ALWAYS_WITHIN_CONSTRAINT:
            case HOLD_DURING_CONSTRAINT:
                intExp.getChildren().add(initExpression(exp.getChildren().get(0), variables, coreProblem));
                intExp.getChildren().add(initExpression(exp.getChildren().get(1), variables, coreProblem));
                intExp.getChildren().add(initExpression(exp.getChildren().get(2), variables, coreProblem));
                break;
            case TIME_VAR:
            case IS_VIOLATED:
                // Do nothing
                break;
            case TASK: // ADD TO DEAL WITH HTN
                final String task = exp.getSymbol().getValue();
                intExp.setSymbol(new Symbol<>(SymbolType.TASK, coreProblem.getTaskSymbols().indexOf(task)));
                intExp.setPrimtive(coreProblem.getPrimitiveTaskSymbols().contains(task));
                args = new ArrayList<>(exp.getArguments().size());
                for (int i = 0; i < exp.getArguments().size(); i++) {
                    final Symbol<String> argument = exp.getArguments().get(i);
                    if (argument.getType().equals(SymbolType.VARIABLE)) {
                        args.add(new Symbol<>(SymbolType.VARIABLE, -variables.indexOf(argument.getValue()) - 1));
                    } else {
                        args.add(new Symbol<>(SymbolType.CONSTANT,
                            coreProblem.getConstantSymbols().indexOf(argument.getValue())));
                    }
                }
                if (exp.getTaskID() != null) { // TaskID is null the task carried out by a method is encoded
                    intExp.setTaskID(new Symbol<>(SymbolType.TASK_ID,
                        Integer.valueOf(exp.getTaskID().getValue().substring(1))));
                }
                intExp.setArguments(args);
                break;
            case LESS_ORDERING_CONSTRAINT:
            case LESS_OR_EQUAL_ORDERING_CONSTRAINT:
            case GREATER_ORDERING_CONSTRAINT:
            case GREATER_OR_EQUAL_ORDERING_CONSTRAINT:
            case EQUAL_ORDERING_CONSTRAINT:
                Expression<Integer> t1 = new Expression<>();
                if (exp.getChildren().get(0).getTimeSpecifier() != null) {
                    t1.setConnector(Connector.TIMED_TASK_ID);
                } else {
                    t1.setConnector(Connector.TASK_ID);
                }
                t1.setTaskID(new Symbol<>(SymbolType.TASK_ID,
                    Integer.valueOf(exp.getChildren().get(0).getTaskID().getValue().substring(1))));
                intExp.addChild(t1);
                Expression<Integer> t2 = new Expression<>();
                if (exp.getChildren().get(0).getTimeSpecifier() != null) {
                    t2.setConnector(Connector.TIMED_TASK_ID);
                } else {
                    t2.setConnector(Connector.TASK_ID);
                }
                t2.setTaskID(new Symbol<>(SymbolType.TASK_ID,
                    Integer.valueOf(exp.getChildren().get(1).getTaskID().getValue().substring(1))));
                intExp.addChild(t2);
                break;
            case HOLD_BEFORE_METHOD_CONSTRAINT:
            case HOLD_AFTER_METHOD_CONSTRAINT:
                final Expression<Integer> t = new Expression<>(Connector.TASK_ID);
                t.setTaskID(new Symbol<>(SymbolType.TASK_ID,
                    Integer.valueOf(exp.getChildren().get(0).getTaskID().getValue().substring(1))));
                intExp.addChild(t);
                intExp.addChild(initExpression(exp.getChildren().get(1), new ArrayList<>(), coreProblem));
                break;
            case HOLD_BETWEEN_METHOD_CONSTRAINT:
                final Expression<Integer> task1 = new Expression<>(Connector.TASK_ID);
                task1.setTaskID(new Symbol<>(SymbolType.TASK_ID,
                    Integer.valueOf(exp.getChildren().get(0).getTaskID().getValue().substring(1))));
                intExp.addChild(task1);
                final Expression<Integer> task2 = new Expression<>(Connector.TASK_ID);
                task2.setTaskID(new Symbol<>(SymbolType.TASK_ID,
                    Integer.valueOf(exp.getChildren().get(1).getTaskID().getValue().substring(1))));
                intExp.addChild(task2);
                intExp.addChild(initExpression(exp.getChildren().get(2), new ArrayList<>(), coreProblem));
                break;
            default:
                // do nothing
        }
        return intExp;
    }

    protected static Goal finalizeGoal(Expression<Integer> intGoal, DefaultProblem coreProblem) {
        Goal goal = new Goal();
            intGoal.toDNF();
            List<Goal> goals = new ArrayList<>(intGoal.getChildren().size());
            for (Expression<Integer> exp : intGoal.getChildren()) {
                if (exp.getConnector().equals(Connector.ATOM)) {
                    Expression<Integer> and = new Expression<>(Connector.AND);
                    and.getChildren().add(exp);
                    goals.add(new Goal(finalizeCondition(and, coreProblem)));
                } else {
                    goals.add(new Goal(finalizeCondition(exp, coreProblem)));
                }
            }
            if (goals.size() > 1) {
                // Create a new dummy fact to encode the goal
                final int dummyPredicateIndex = coreProblem.getPredicateSymbols().size();
                coreProblem.getPredicateSymbols().add(Constants.DUMMY_GOAL);
                coreProblem.getPredicateSignatures().add(new ArrayList<>());
                Expression<Integer> dummyGoal = new Expression<>(Connector.ATOM);
                dummyGoal.setSymbol(new Symbol<>(SymbolType.PREDICATE, dummyPredicateIndex));
                dummyGoal.setArguments(new ArrayList<>(0));
                final int dummyGoalIndex = coreProblem.getIntExpFluents().size();
                coreProblem.getIntExpFluents().add(dummyGoal);
                coreProblem.getMapOfNumericFluentIndex().put(dummyGoal, dummyGoalIndex);
                Effect effect = new Effect();
                effect.getPositiveFluents().set(dummyGoalIndex);
                goal = new Goal();
                effect.getPositiveFluents().set(dummyGoalIndex);
                final ConditionalEffect condEffect = new ConditionalEffect(effect);
                // for each disjunction create a dummy action
                for (Condition dis : goals) {
                    final Action op = new Action(Constants.DUMMY_OPERATOR, 0);
                    op.setDummy(true);
                    op.setPrecondition(dis);
                    op.getConditionalEffects().add(condEffect);
                    coreProblem.getActions().add(op);
                }
            } else {
                goal = goals.get(0);
            }

            return goal;
        
    }

    /**
     * Encode an specified <code>Expression</code> that represents a condition in
     * its <code>BitExp</code>
     * representation. The map of fluent index is used to speed-up the encoding.
     *
     * @param exp the <code>Expression</code>.
     * @return the condition encoded.
     */
    protected static Condition finalizeCondition(final Expression<Integer> exp, DefaultProblem coreProblem) throws UnexpectedExpressionException {
        final Condition condition = new Condition();
        switch (exp.getConnector()) {
            case ATOM:
                condition.getPositiveFluents().set(coreProblem.getMapOfFluentIndex().get(exp));
                break;
            case NOT:
                condition.getNegativeFluents().set(coreProblem.getMapOfFluentIndex().get(exp.getChildren().get(0)));
                break;
            case AND:
                for (Expression<Integer> e : exp.getChildren()) {
                    Condition ce = finalizeCondition(e, coreProblem);
                    condition.getPositiveFluents().or(ce.getPositiveFluents());
                    condition.getNegativeFluents().or(ce.getNegativeFluents());
                    condition.getNumericConstraints().addAll(ce.getNumericConstraints());
                }
                break;
            case LESS_COMPARISON:
            case LESS_OR_EQUAL_COMPARISON:
            case GREATER_COMPARISON:
            case GREATER_OR_EQUAL_COMPARISON:
            case TRUE:
                // do nothing
                break;
            default:
                throw new UnexpectedExpressionException(exp.getConnector().toString());
        }
        return condition;
    }

    /**
     * Returns the string representation of a list of types.
     *
     * @param types the list of types.
     * @return the string representation of this type.
     */
    private static String toStringType(final List<Symbol<String>> types) {
        final StringBuilder str = new StringBuilder();
        if (types.size() > 1) {
            str.append("either");
            for (Symbol<String> type : types) {
                str.append("~");
                str.append(type.getValue());
            }
        } else {
            str.append(types.get(0).getValue());
        }
        return str.toString();
    }
}
