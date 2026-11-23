# Isolated vertices are rare beyond $e^{-c}$

Let $c \in \mathbb{R}$ and let $p_n \in [0, 1]$ satisfy $n p_n - \log n \to c$, for instance $p_n = (\log n + c)/n$ for all large $n$. Then for every $\delta > 0$, for all large $n$,

$$\Pr[G(n, p_n) \text{ has an isolated vertex}] \le e^{-c} + \delta.$$

This is the first-moment method: the probability is at most the expected number of isolated vertices, which tends to $e^{-c}$. The true limit, $1 - e^{-e^{-c}}$, is smaller than $e^{-c}$; it is the [Poisson statement](tendsto-measure-real-no-isolated.md), Theorem 3.1 (ii) of the source.

## Informally uses

- [First moment bound for isolated vertices of $G(n, p)$](measure-real-exists-isolated-le.md): the union bound.
- [First moment of isolated vertices at the connectivity threshold](tendsto-mul-one-sub-pow.md): the limit of the bound.

## Sources

- A. Frieze and M. Karoński, *Introduction to Random Graphs*, Cambridge University Press (2016), Section 3.1.
