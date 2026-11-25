# Uniqueness for martingale problems by duality

Let $E$ and $F$ be measurable spaces and $H:E\times F\to\mathbb R$ bounded and measurable, such that the family $\{H(\cdot,y):y\in F\}$ is measure-determining on $E$: two probability measures $\nu_1,\nu_2$ on $E$ with $\int H(x,y)\,\nu_1(dx)=\int H(x,y)\,\nu_2(dx)$ for all $y$ are equal. Fix, before considering any solution, a Markov family $(Y,(\mathbb P^y)_{y\in F})$ on $F$. Suppose that for every initial law $\mu$, every solution $X$ of the $(A,\mu)$ [martingale problem](martingale-problems-generic-definition.md) in the path class considered, every $t\ge0$ and every $y\in F$,

$$\mathbb E\bigl[H(X_t,y)\bigr]=\int_E\mathbb E^y\bigl[H(x,Y_t)\bigr]\,\mu(dx).$$

Then for every $\mu$, any two solutions of the $(A,\mu)$ martingale problem have the same one-time marginals, and therefore, by [the one-time-to-finite-dimensional lemma](from-one-time-marginal-uniqueness-to-fdd-uniquen.md), the same finite-dimensional distributions: uniqueness holds.

The dual family must not depend on the candidate solution, and the duality identity must hold for every solution and every initial law, since the lemma is applied to tilted initial laws.

## Depends on

- [Uniqueness of one-time marginals implies uniqueness of finite-dimensional distributions for martingale problems](from-one-time-marginal-uniqueness-to-fdd-uniquen.md)
- [Martingale problems](martingale-problems-generic-definition.md)

## Expansion

A full proof page must establish:

- The right-hand side of the duality identity does not involve the solution, so $\mathbb E\,H(X_t,y)=\mathbb E\,H(X'_t,y)$ for two solutions and all $y$; the measure-determining property gives equal laws of $X_t$ and $X'_t$.
- Measurability and integrability of $(x,\omega)\mapsto H(x,Y_t(\omega))$, so the right-hand side is defined.
- The application of the one-time-to-finite-dimensional lemma, which needs one-time uniqueness for every initial law.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986), <https://onlinelibrary.wiley.com/doi/book/10.1002/9780470316658>, Ch. 4 (duality).
