# CDCL certificates of pigeonhole formulas are exponential

There is an absolute constant $\epsilon > 0$ such that for every $n$ and every numbering of the variables of $\mathrm{PHP}^{n+1}_n$, every LRAT certificate for $\mathrm{PHP}^{n+1}_n$ built from RUP steps, in particular the certificate returned by the CDCL solver, has total size $H + S \cdot N$ at least $2^{\epsilon n} - |\mathrm{PHP}^{n+1}_n|$, where $H$ is its number of hints, $S$ its number of steps, $N = n(n+1)$ the number of variables and $|\mathrm{PHP}^{n+1}_n|$ the number of clauses. In fact $\min(H, S \cdot N) \ge 2^{\epsilon n} - |\mathrm{PHP}^{n+1}_n|$. (Haken's bound holds for all $n \ge n_0$; decreasing $\epsilon$ makes the right side nonpositive for $n < n_0$, so the bound holds for every $n$.)

## Proof sketch

The certificate translates into a resolution refutation with at most $|\mathrm{PHP}^{n+1}_n| + \min(H, S \cdot N)$ clauses, and by Haken's theorem every resolution refutation of $\mathrm{PHP}^{n+1}_n$ has at least $2^{\epsilon n}$ clauses.

## Depends on

- [A CDCL solver with watched literals returns models or LRAT refutations](../cdcl-sat-solver-components/certified-cdcl-solver-correctness.md)
- [Haken's lower bound for the pigeonhole principle](../../../Logic/propositional-logic/propositional-proof-complexity/haken-s-lower-bound-for-the-pigeonhole-principle.md)
- [Pigeonhole formulas $\mathrm{PHP}^m_n$](../../../Logic/proof-theory/resolution-lower-bounds/pigeonhole-formulas.md)

## Proof depends on

- [Accepted LRAT certificates translate into resolution refutations](../../../Logic/propositional-logic/proof-certificates/clausal-proof-certificates/lrat-certificates-to-resolution.md)

## Sources

- A. Haken, "The Intractability of Resolution", Theoretical Computer Science 39, 1985.
- L. Cruz-Filipe, M. J. H. Heule, W. A. Hunt Jr., M. Kaufmann and P. Schneider-Kamp, "Efficient Certified RAT Verification", Automated Deduction (CADE-26), LNCS 10395, Springer, 2017.
