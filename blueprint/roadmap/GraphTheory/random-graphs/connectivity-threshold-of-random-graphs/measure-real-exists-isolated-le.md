# First moment bound for isolated vertices of $G(n, p)$

For every $n$ and $p \in [0, 1]$,

$$\Pr[G(n, p) \text{ has an isolated vertex}] \le n(1 - p)^{n-1},$$

the expected number of isolated vertices, where $n - 1$ is read as $0$ when $n = 0$ (both sides are then $0$). This is the union bound over the $n$ vertices.

## Informally uses

- [Probability that a vertex of $G(n, p)$ is isolated](measure-real-isolated.md): each term of the union bound.

## Sources

- A. Frieze and M. Karoński, *Introduction to Random Graphs*, Cambridge University Press (2016), Section 3.1: $\mathbb{E} X_0 = \sum_v \mathbb{E} I_v = n(1-p)^{n-1}$, in (3.3).
