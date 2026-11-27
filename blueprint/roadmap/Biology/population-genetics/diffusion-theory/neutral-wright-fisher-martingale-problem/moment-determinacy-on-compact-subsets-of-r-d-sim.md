# Moment determinacy on compact subsets of Euclidean space

Let $E \subseteq \mathbb R^d$ be compact, for example the simplex $\Delta_{K-1}$ or the product $\Delta_{K-1}^k$ that carries the joint law of a process on $\Delta_{K-1}$ at $k$ times. If two finite Borel measures $\mu$ and $\nu$ on $E$ have the same mixed moments,

$$\int_E x^\beta\, \mu(dx) = \int_E x^\beta\, \nu(dx) \qquad \text{for every multi-index } \beta \in \mathbb N_0^d,$$

then $\mu = \nu$.

Equivalently, let $\mu$ and $\nu$ be finite Borel measures on $\mathbb R^d$ with $\mu(\mathbb R^d \setminus E) = \nu(\mathbb R^d \setminus E) = 0$ whose mixed moments $\int \prod_i x_i^{\beta_i}\, d\mu(x)$ and $\int \prod_i x_i^{\beta_i}\, d\nu(x)$ agree for every $\beta$; then $\mu = \nu$. The two formulations correspond by pushing a measure on $E$ forward along the inclusion into $\mathbb R^d$, which gives a measure with no mass off $E$, and by restricting a measure on $\mathbb R^d$ to $E$; since $E$ is closed these operations are inverse, preserve every mixed moment (the moment with $\beta = 0$ being the total mass) and reflect equality of measures. The declaration states the second formulation.

By the Stone–Weierstrass theorem the polynomials are dense in $C(E)$, so $\int f\, d\mu = \int f\, d\nu$ for every $f \in C(E)$, and finite Borel measures on a compact metric space are determined by their integrals of continuous functions.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley, 1986, Chapter 4, Section 4 (the moment method), <https://doi.org/10.1002/9780470316658> (background)
