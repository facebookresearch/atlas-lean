# Certificates from abstract DPLL with learning

Consider a derivation $\emptyset \parallel F \Longrightarrow^*_{\mathcal{L}} S$ in [abstract DPLL with learning](abstract-dpll-with-learning.md).

1. **Models.** If $S = M \parallel F'$ is final with respect to Basic DPLL, then the assignment $M$ is a model of $F$. Checking it takes time linear in the size of $F$.
2. **Refutations.** If $S$ is FailState, then $F$ is unsatisfiable. A resolution refutation of $F$ can be produced from the run when each step records how its clause was obtained:
    - every learned clause and backjump clause records a resolution derivation from the current clauses;
    - every propagated literal records the clause that propagated it.

    The refutation then has size linear in the recorded derivations plus the number of propagation steps.

Part 1 and the unsatisfiability claim of part 2 are the [final-state theorem](final-states-of-abstract-dpll-with-learning.md). The abstract rules Learn and Backjump only require semantic entailment, $F \models C$. A certificate is therefore available only for strategies that record derivations, as conflict analysis by resolution over propagation reasons does in practice.

## Depends on

- [Abstract DPLL with learning](abstract-dpll-with-learning.md)
- [Final states of abstract DPLL with learning](final-states-of-abstract-dpll-with-learning.md)

## Expansion

This page becomes ready once these are stated:

- the recording discipline as a refinement of the transition system, with each Learn and Backjump step carrying a resolution derivation (statement prerequisite);
- the construction of the refutation from the recorded derivations at FailState, by resolving the final conflicting clause against the reasons of the level-0 literals (proof prerequisite).

## Sources

- R. Nieuwenhuis, A. Oliveras and C. Tinelli, "Solving SAT and SAT modulo theories: from an abstract Davis–Putnam–Logemann–Loveland procedure to DPLL(T)", *Journal of the ACM* 53(6):937–977, 2006, <https://www.cs.upc.edu/~roberto/papers/JACM2006.pdf>, Section 2: Definition 2.5 (Learn and Forget with side condition $F \models C$), Definition 2.4 (Backjump with $F, C \models C' \vee l'$), and Theorem 2.12 (models from final states, FailState if and only if unsatisfiable), together with Example 2.6 (finding backjump clauses from the conflict graph of propagation reasons).
