# Moment determinacy on compact subsets of Euclidean space

Let $E \subseteq \mathbb R^d$ be compact, for example the simplex $\Delta_{K-1}$ or the product $\Delta_{K-1}^k$ that carries the joint law of a process on $\Delta_{K-1}$ at $k$ times. If two finite Borel measures $\mu$ and $\nu$ on $E$ have the same mixed moments,

$$\int_E x^\beta\, \mu(dx) = \int_E x^\beta\, \nu(dx) \qquad \text{for every multi-index } \beta \in \mathbb N_0^d,$$

then $\mu = \nu$. By the Stone–Weierstrass theorem the polynomials are dense in $C(E)$, so $\int f\, d\mu = \int f\, d\nu$ for every $f \in C(E)$, and finite Borel measures on a compact metric space are determined by their integrals of continuous functions.

## Proof depends on

- [Stone–Weierstrass theorem for star subalgebras](../../../../Topology/function-spaces/stone-weierstrass-star-subalgebra.md)
- [Finite Borel measures on a metric space are determined by integrals of bounded continuous functions](../../../../MeasureTheory/measures/regular-measures/measures-determined-by-continuous-integrals.md)

## Expansion

A full proof page must still establish the density of polynomials in $C(E)$ and the identification of finite Borel measures on $E$ from their integrals of continuous functions, and record the case $E = \Delta_{K-1}^k \subseteq \mathbb R^{kK}$.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley, 1986, Chapter 4, Section 4 (the moment method), <https://doi.org/10.1002/9780470316658> (background)
