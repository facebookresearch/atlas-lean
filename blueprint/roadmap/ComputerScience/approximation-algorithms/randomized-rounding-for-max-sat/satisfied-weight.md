# Weight satisfied by a truth assignment

For a truth assignment $a$, the total weight $\sum_{j : a \models C_j} w_j$ of the clauses it
[satisfies](../../../Logic/propositional-logic/conjunctive-normal-form/satisfies-2.md), where $a \models C_j$ means that some literal of $C_j$ is true under $a$. MAX SAT
maximizes it over $a$.

## Background

- [MAXIMUM SATISFIABILITY is NP-complete](../../../TheoryOfComputation/np-completeness/satisfiability/maximum-satisfiability/max-sat-np-complete.md):
  the decision version of this maximization.
