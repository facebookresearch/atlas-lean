# Balance, spread and load of nearest-point consistent hashing

Let the number of buckets in any view be less than $C$, and let the [nearest-point construction](monotonicity-of-nearest-point-consistent-hashing.md) give each bucket $\kappa \log C$ replicas, for a suitable constant $\kappa$, with $r_{\mathcal B}$ and $r_{\mathcal I}$ mapping points $\log C$-way independently and uniformly to $[0, 1]$. The resulting family $\mathcal F$ is monotone and has the following [balance, spread and load](balance-spread-and-load-of-ranged-hash-families.md) properties.

1. **Balance.** For a fixed view $\mathcal V$, $\Pr[f_{\mathcal V}(i) = b] \le O(1/|\mathcal V|)$ for every item $i$ and bucket $b \in \mathcal V$, and, conditioned on the choice of $r_{\mathcal B}$, the assignments of items to buckets are $\log C$-way independent.
2. **Spread.** For views as in the definition of spread, each containing at least $C/t$ buckets, if the number of views is $V = \rho C$ for some constant $\rho$ and the number of items is $I = C$, then the spread of each item is $O(t \log C)$ with probability greater than $1 - 1/C^{\Omega(1)}$.
3. **Load.** Under the same conditions the load of each bucket is $O(t \log C)$ with probability greater than $1 - 1/C^{\Omega(1)}$.

## Depends on

- [Balance, spread and load of ranged hash families](balance-spread-and-load-of-ranged-hash-families.md)
- [Monotonicity of nearest-point consistent hashing](monotonicity-of-nearest-point-consistent-hashing.md)

## Expansion

This page becomes ready once these prerequisites are stated and checked against the full version of the source, which the conference paper defers to:

- $k$-wise independent uniform maps to the unit interval and the Chernoff bounds for them used in the proof (statement and proof prerequisites);
- the precise roles of the constants $\kappa$, $\rho$ and $t$ in the high-probability bounds;
- the balance argument: with $\kappa \log C$ random points per bucket, each bucket is responsible for at most an $O(1/|\mathcal V|)$ fraction of the interval with high probability.

## Sources

- D. Karger, E. Lehman, T. Leighton, R. Panigrahy, M. Levine and D. Lewin, "Consistent hashing and random trees: distributed caching protocols for relieving hot spots on the World Wide Web", *Proceedings of the 29th Annual ACM Symposium on Theory of Computing*, 654–663, 1997, Section 4.2, Theorem 4.1 (properties 1–4) with its proof sketch, and Corollary 4.2.
