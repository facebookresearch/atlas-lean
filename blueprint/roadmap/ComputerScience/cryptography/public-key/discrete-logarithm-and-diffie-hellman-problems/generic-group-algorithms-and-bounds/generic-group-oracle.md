# Generic group oracle with labelings

In the generic group model for a cyclic group of order $q$, the oracle holds a uniformly random injective labeling $L : \mathbb{Z}_q \to S$ into a finite label set $S$ with $|S| \ge q$. It answers a labeling query $\beta$ with $L(\beta)$, and a group-operation query $(\ell_1, \ell_2, \kappa_1, \kappa_2)$ with $L(\kappa_1\beta_1 + \kappa_2\beta_2)$ when $\ell_i = L(\beta_i)$, rejecting labels outside the image. A generic algorithm accesses group elements only through labels and the oracle; its cost counts group-operation queries.

## Depends on

- [Shoup's generic lower bound for discrete logarithms](../../hardness-assumptions/shoup-s-generic-lower-bound-for-discrete.md)
- [Adaptive oracle algorithms](../../../security-games/oracle-algorithms/oracle-comp.md)

## Sources

- V. Shoup, "Lower Bounds for Discrete Logarithms and Related Problems", Advances in Cryptology (EUROCRYPT 1997), LNCS 1233, 1997.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
