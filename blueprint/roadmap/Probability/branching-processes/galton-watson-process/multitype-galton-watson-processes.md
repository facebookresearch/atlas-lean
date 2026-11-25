# Mean identity for multitype Galton–Watson processes

Let $K \ge 1$ types be given and, for each type $i$, an offspring law on $\mathbb N^K$ with finite mean vector $M_{i\cdot}$, so that the mean matrix
$M = (M_{ij})$ records the expected number of type-$j$ children of a type-$i$ individual. In the multitype Galton–Watson process each
individual of generation $n$ reproduces independently with the offspring law of its type, and $Z_{n+1} \in \mathbb N^K$ counts the children by type.
Then for every integrable initial population $Z_0$ (deterministic, random, or zero)

$$\mathbb E[Z_n \mid Z_0] = Z_0\, M^n \qquad (n \ge 0),$$

because $\mathbb E[Z_{n+1} \mid Z_0, \dots, Z_n] = Z_n M$ by summing the conditional means of the independent offspring vectors. For $K = 1$ and $Z_0 = 1$ it
gives $\mathbb E Z_n = m^n$ for the [mean offspring number](mean.md) $m$. For $Z_0 = 0$ it is the trivial $Z_n = 0$. For two islands whose individuals have
$\mathrm{Poisson}(m(1 - \mu))$ children on their own island and, independently, $\mathrm{Poisson}(m\mu)$ on the other, $M = m\begin{pmatrix} 1 - \mu & \mu \\ \mu & 1 - \mu \end{pmatrix}$ and
$Z_0 = (1, 0)$ give $\mathbb E Z_n = \frac{m^n}{2}\bigl(1 + (1 - 2\mu)^n,\ 1 - (1 - 2\mu)^n\bigr)$.

## Depends on

- [Mean offspring number](mean.md)

## Expansion

The extinction dichotomy (for a nonzero deterministic start, a primitive mean matrix with Perron root $\rho$ and a nonsingular process,
extinction is almost sure if and only if $\rho \le 1$) needs the Perron–Frobenius theorem and the multitype generating-function fixed point;
it is a separate statement. With $Z_0 = 0$ it fails trivially, since extinction is certain whatever $\rho$ is.

## Sources

- K. B. Athreya and P. E. Ney, *Branching Processes*, Springer (1972), Chapter V. The mean identity is derived above.
