# Increment bound and continuous modification on the simplex

Let $K \ge 2$ and let $\Delta_{K-1} = \{x \in [0,1]^K : \sum_i x_i = 1\}$ be the closed simplex. Under the [canonical path measure of the neutral $K$-allele Wright–Fisher process](k-allele-transition-kernel-and-canonical-path-me.md) $P_x$, $x \in \Delta_{K-1}$, the coordinate process $X = (X^1, \dots, X^K)$ satisfies

$$\mathbb E_x\bigl[(X^i_t - X^i_s)^4\bigr] \le C_K\, |t - s|^2 \qquad \text{for all } s, t \ge 0 \text{ and } i = 1, \dots, K,$$

with a constant $C_K$ computed from the simplex generator applied to the polynomials $y \mapsto (y_i - x_i)^4$. By Kolmogorov's continuity theorem applied to each real coordinate, $X$ has a modification with continuous paths, and since each $X_t$ lies in $\Delta_{K-1}$ almost surely and $\Delta_{K-1}$ is closed, the modification can be taken $\Delta_{K-1}$-valued.

## Depends on

- [K-allele transition kernel and canonical path measure on the simplex](k-allele-transition-kernel-and-canonical-path-me.md)

## Proof depends on

- [Neutral K-allele semigroup on the simplex via multinomial duality](../wright-fisher-semigroup-and-moment-duality/neutral-k-allele-semigroup-on-the-simplex-via-mu.md)

## Expansion

A full proof page must still establish:

- the computation of the generator on $(y_i - x_i)^4$ and $(y_i - x_i)^2$ and the resulting bound with $C_K$ explicit;
- the coordinatewise use of the Kolmogorov–Chentsov theorem and the closedness argument that keeps the modification in the simplex.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley, 1986, Chapter 10, <https://doi.org/10.1002/9780470316658>
