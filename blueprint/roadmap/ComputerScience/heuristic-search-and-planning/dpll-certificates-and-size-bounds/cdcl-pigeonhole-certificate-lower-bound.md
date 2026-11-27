# CDCL certificates of pigeonhole formulas are exponential

There are an absolute constant $\epsilon > 0$ and an $n_0$ such that for every $n \ge n_0$ and every numbering of the variables of $\mathrm{PHP}^{n+1}_n$ the following holds. In every run of the CDCL solver on $\mathrm{PHP}^{n+1}_n$ that reports unsatisfiability, each learned clause is a RUP clause for the clauses present when it is learned, and so has a trivial resolution derivation from them; these derivations together form a resolution refutation of $\mathrm{PHP}^{n+1}_n$, which has at least $2^{\epsilon n}$ clauses. Hence the trivial derivations behind the learned clauses contain at least $2^{\epsilon n} - |\mathrm{PHP}^{n+1}_n|$ derived clauses in total, where $|\mathrm{PHP}^{n+1}_n|$ is the number of clauses of the formula. That CDCL runs yield resolution refutations, and that a formula exponentially hard for resolution cannot be solved fast by CDCL, are stated by Buss and Nordström (Sections 7.3.1.3, 7.3.2 and 7.3.3); the lower bound for $\mathrm{PHP}^{n+1}_n$ is Haken's.

## Proof sketch

The learned clauses, each derived from earlier clauses by a trivial resolution derivation, followed by the final conflict at decision level $0$, give a resolution refutation with at most $|\mathrm{PHP}^{n+1}_n|$ input clauses plus the derived ones, and by Haken's theorem every resolution refutation of $\mathrm{PHP}^{n+1}_n$ has at least $2^{\epsilon n}$ clauses. Derived through the translation of accepted LRAT certificates into resolution refutations, not stated by the sources: every LRAT certificate for $\mathrm{PHP}^{n+1}_n$ built from RUP steps, in particular the one the solver returns, satisfies $\min(H, S \cdot N) \ge 2^{\epsilon n} - |\mathrm{PHP}^{n+1}_n|$, where $H$ is its number of hints, $S$ its number of steps and $N = n(n+1)$ the number of variables.

## Depends on

- [A CDCL solver with watched literals returns models or LRAT refutations](../cdcl-sat-solver-components/certified-cdcl-solver-correctness.md)
- [Haken's lower bound for the pigeonhole principle](../../../Logic/propositional-logic/propositional-proof-complexity/haken-s-lower-bound-for-the-pigeonhole-principle.md)
- [Pigeonhole formulas $\mathrm{PHP}^m_n$](../../../Logic/proof-theory/resolution-lower-bounds/pigeonhole-formulas.md)
- [Trivial resolution derivations](../../../Logic/propositional-logic/proof-certificates/clausal-proof-certificates/trivial-resolution-derivations.md)
- [Resolution refutation](../../../Logic/propositional-logic/resolution-size-and-width/is-resolution-refutation.md)

## Proof depends on

- [RUP steps and resolution steps simulate each other](../../../Logic/propositional-logic/proof-certificates/clausal-proof-certificates/lrat-certificates-to-resolution.md)

## Sources

- A. Haken, "The Intractability of Resolution", Theoretical Computer Science 39, 1985.
- S. Buss and J. Nordström, "Proof Complexity and SAT Solving", in A. Biere, M. Heule, H. van Maaren and T. Walsh (eds.), Handbook of Satisfiability, 2nd edition, IOS Press, 2021, Chapter 7 (Sections 7.3.1.3, 7.3.2, 7.3.3 and 7.4.1).
- L. Cruz-Filipe, M. J. H. Heule, W. A. Hunt Jr., M. Kaufmann and P. Schneider-Kamp, "Efficient Certified RAT Verification", Automated Deduction (CADE-26), LNCS 10395, Springer, 2017.
