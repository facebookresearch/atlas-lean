# Semigroup-free uniqueness: conditional polynomial identities determine finite-dimensional laws

Let $E \subseteq \mathbb R^d$ be compact, let $A$ be a linear operator that maps the polynomials of degree at most $n$ into themselves for every $n$, and let $X$ solve the martingale problem for $A$ on polynomials, with any initial law, so that by the [conditional polynomial-semigroup identity](conditional-polynomial-semigroup-identity-for-ma.md) $\mathbb E[p(X_t) \mid \mathcal F_s] = (e^{(t-s)A} p)(X_s)$ for polynomials $p$ and $s \le t$. For times $0 \le t_1 < \dots < t_k$ and polynomials $p_1, \dots, p_k$, conditioning on $\mathcal F_{t_{k-1}}$ gives

$$\mathbb E\Bigl[\prod_{i=1}^k p_i(X_{t_i})\Bigr] = \mathbb E\Bigl[\prod_{i=1}^{k-2} p_i(X_{t_i}) \cdot q(X_{t_{k-1}})\Bigr], \qquad q = p_{k-1} \cdot e^{(t_k - t_{k-1})A} p_k,$$

and $q$ is again a polynomial, of degree at most $\deg p_{k-1} + \deg p_k$. By backward recursion every joint polynomial moment of $(X_{t_1}, \dots, X_{t_k})$ equals $\mathbb E[r(X_0)]$ for a polynomial $r$ that depends only on $A$, the times and the $p_i$. Hence two solutions with the same initial law have the same joint polynomial moments, and by [moment determinacy](moment-determinacy-on-compact-subsets-of-r-d-sim.md) on $E^k$ the same finite-dimensional laws. For $k = 1$, $\mathbb E\, p(X_t) = \mathbb E\, (e^{tA} p)(X_0)$. No transition semigroup, kernel or existence statement is assumed or produced.

## Depends on

- [Conditional polynomial-semigroup identity for martingale-problem solutions with triangular generators](conditional-polynomial-semigroup-identity-for-ma.md)
- [Moment determinacy on compact subsets of Euclidean space](moment-determinacy-on-compact-subsets-of-r-d-sim.md)
- [Conditional expectation given a σ-field](../../../../Probability/foundations/conditional-expectation/conditional-expectation-given-a-sigma-field/conditional-expectation.md)

## Proof depends on

- [Martingale problems (generic definition)](../../../../Probability/markov-chains/martingale-problems/martingale-problems-generic-definition.md)
- [Tower property of conditional expectation](../../../../Probability/foundations/conditional-expectation/tower-property/tower-property.md)

## Expansion

A full proof page must still establish the recursion with its degree bookkeeping and the passage from joint polynomial moments to finite-dimensional laws.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley, 1986, Chapter 4 (duality and uniqueness by moments), <https://doi.org/10.1002/9780470316658>
