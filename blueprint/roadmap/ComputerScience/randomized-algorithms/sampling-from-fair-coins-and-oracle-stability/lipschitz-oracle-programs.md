# Oracle programs are Lipschitz in their oracle's reply distributions

Let $A$ be a probabilistic oracle program making at most $q$ queries on every path, and let $O, O'$ be (possibly stateful) oracles such that for every query and state the reply distributions satisfy $\Delta(O(\cdot), O'(\cdot)) \le \varepsilon$. Then the output distributions satisfy

$$\Delta\bigl(A^{O}, A^{O'}\bigr) \le q\,\varepsilon.$$

More generally, a program is $K$-Lipschitz at $O$ if $\Delta(A^O, A^{O'}) \le K\varepsilon$ for all such $O'$, and $K = q$ always works.

## Proof sketch

Hybrid over the queries: the $i$-th hybrid answers the first $i$ queries with $O'$ and the rest with $O$. Adjacent hybrids differ in the reply law of one query, and post-processing cannot increase statistical distance.

## Depends on

- [Probabilistic oracle program and its semantics against a stateful handler](../../cryptography/security-games/probabilistic-oracle-programs/probabilistic-oracle-program.md)
- [Total variation distance between finite measures](../../../Probability/convergence-of-measures/total-variation-distance/total-variation-dist.md)

## Proof depends on

- [Hybrid argument](../../cryptography/security-games/games-and-advantages/advantage-le-sum.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
