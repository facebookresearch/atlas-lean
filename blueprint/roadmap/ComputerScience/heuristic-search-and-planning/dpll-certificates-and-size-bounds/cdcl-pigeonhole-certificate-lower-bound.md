# CDCL certificates of pigeonhole formulas are exponential

There is an absolute constant $\epsilon > 0$ such that for every $n$ and every numbering of the variables of $\mathrm{PHP}^{n+1}_n$, every LRAT certificate for $\mathrm{PHP}^{n+1}_n$ built from RUP steps, in particular the certificate returned by the CDCL solver, has total size $H + S \cdot N$ at least $2^{\epsilon n} - |\mathrm{PHP}^{n+1}_n|$, where $N = n(n+1)$; one admissible choice is $\epsilon = 1/24$.

## Proof sketch

Translate the certificate into a resolution refutation with the LRAT-to-resolution bound and apply Haken's exponential lower bound on resolution refutations of the pigeonhole principle.

## Depends on

- [A CDCL solver with watched literals returns models or LRAT refutations](../cdcl-sat-solver-components/certified-cdcl-solver-correctness.md)
- [Haken's lower bound for the pigeonhole principle](../../../Logic/propositional-logic/propositional-proof-complexity/haken-s-lower-bound-for-the-pigeonhole-principle.md)

## Proof depends on

- [Accepted LRAT certificates translate into resolution refutations](../../../Logic/propositional-logic/proof-certificates/clausal-proof-certificates/lrat-certificates-to-resolution.md)
- [Haken's lower bound for the pigeonhole principle](../../../Logic/propositional-logic/propositional-proof-complexity/haken-s-lower-bound-for-the-pigeonhole-principle.md)

## Sources

- A. Haken, "The Intractability of Resolution", Theoretical Computer Science 39, 1985.
- L. Cruz-Filipe, M. J. H. Heule, W. A. Hunt Jr., M. Kaufmann and P. Schneider-Kamp, "Efficient Certified RAT Verification", Automated Deduction (CADE-26), LNCS 10395, Springer, 2017.
