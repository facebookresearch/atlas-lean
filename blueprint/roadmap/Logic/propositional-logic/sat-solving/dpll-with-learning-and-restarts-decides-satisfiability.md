# DPLL with learning and restarts decides satisfiability

Let $F$ be a CNF formula, and run [abstract DPLL with learning](abstract-dpll-with-learning.md), with or without Restart, from $\emptyset \parallel F$. Suppose the strategy satisfies three conditions:
- the run does not stop while some Basic DPLL rule applies;
- it creates no infinite subderivation consisting only of Learn and Forget steps;
- if Restart is used, it has increasing periodicity.

Then every run reaches a state $S$ that is final with respect to Basic DPLL, and:
- $S$ is FailState exactly when $F$ is unsatisfiable;
- otherwise $S$ is $M \parallel F'$ with $M$ a model of $F$.

So these systems are decision procedures for propositional satisfiability. Conflict-driven solvers apply Learn only to backjump clauses and Forget only to learned lemmas, so they satisfy the second condition; the first and third are properties of the strategy that must be checked separately.

**Proof.** By [termination](termination-of-abstract-dpll-with-learning.md), every such run is finite, and its last state admits no Basic DPLL step. The [final-state theorem](final-states-of-abstract-dpll-with-learning.md) then characterizes that state.

## Depends on

- [Termination of abstract DPLL with learning](termination-of-abstract-dpll-with-learning.md)
- [Final states of abstract DPLL with learning](final-states-of-abstract-dpll-with-learning.md)

## Sources

- R. Nieuwenhuis, A. Oliveras and C. Tinelli, "Solving SAT and SAT modulo theories: from an abstract Davis–Putnam–Logemann–Loveland procedure to DPLL(T)", *Journal of the ACM* 53(6):937–977, 2006, <https://www.cs.upc.edu/~roberto/papers/JACM2006.pdf>, Section 2.5: Theorem 2.11 and its remark that the condition is weak and easily enforced, Theorem 2.12, Theorem 2.16, and the concluding statement that these systems provide a decision procedure for propositional satisfiability.
