# Interpolation-based model checking

Let $M = (I, T, F)$ be a finite transition system with initial states $I$, total transition relation $T$ and final (bad) states $F$, and $k > 0$. McMillan's procedure FiniteRun$(M, k)$ returns True if $I \wedge F$ is satisfiable; otherwise it sets $R = I$ and repeats: if the bounded model checking formula that starts from $R$ with one transition step followed by up to $k$ further steps and reaches $F$ is satisfiable, it returns True when $R = I$ and aborts otherwise; if that formula is unsatisfiable, it takes an interpolant $P$ of its refutation for the split between the first transition step and the rest, renamed to the current-state variables, returns False if $P$ implies $R$, and otherwise replaces $R$ by $R \vee P$. Then:

1. if FiniteRun$(M, k)$ terminates without aborting, it returns True exactly when some run of $M$ from $I$ reaches $F$;
2. for every $M$ there is a $k$ for which FiniteRun$(M, k)$ terminates, namely every $k > 0$ at least the reverse depth of $M$: the largest length of a shortest path to $F$ over the states from which $F$ is reachable, and $0$ if no state reaches $F$.

## Proof depends on

- [Interpolants from resolution refutations](../../../Logic/propositional-logic/proof-certificates/interpolants-from-resolution-refutations.md)
- [Bounded model checking for existential LTL](bounded-model-checking-for-existential-ltl.md)
- [Interpolants of bounded model checking refutations over-approximate images](interpolants-of-bounded-model-checking.md)

## Sources

- K. L. McMillan, "Interpolation and SAT-based model checking", *CAV 2003*, LNCS 2725, Springer, 2003, Section 4, Figure 3 and Theorems 3 and 4, <https://people.eecs.berkeley.edu/~alanmi/courses/2008_290A/papers/mcmillan_cav03.pdf>
