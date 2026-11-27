# Schöning's random-walk trial

Let $\varphi$ be a CNF formula over variables $x_1, \dots, x_n$ in which every clause has at most $k$ literals. One **Schöning trial** draws an assignment $\sigma \in \{0,1\}^n$ uniformly at random and then performs at most $3n$ local steps: if $\sigma$ satisfies $\varphi$ it stops and returns $\sigma$; otherwise it takes the first clause $C$ of $\varphi$ falsified by $\sigma$, picks one of the literals of $C$ uniformly at random, and flips the value of its variable. A trial **succeeds** if it returns a satisfying assignment.

## Depends on

- [CNF formula](../../../Logic/propositional-logic/conjunctive-normal-form/cnf.md)
- [Satisfiability of a CNF formula](../../../Logic/propositional-logic/conjunctive-normal-form/cnfsat.md)

## Sources

- U. Schöning, "A Probabilistic Algorithm for k-SAT and Constraint Satisfaction Problems", 40th IEEE Symposium on Foundations of Computer Science (FOCS), 1999.
