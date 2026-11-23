# Mantel's theorem from Goodman's bound

A triangle-free finite simple graph with $n$ vertices and $m$ edges satisfies $4m \le n^2$, that is, it has at most $n^2/4$ edges.

The proof is the flag-algebra one. With no triangles, [Goodman's bound](goodman.md) gives $m(4m - n^2) \le 0$, so $m = 0$ or $4m \le n^2$. The bound is also a quick corollary of Turán's theorem, which gives $m \le t(n, 2) = \lfloor n^2/4 \rfloor$ for the number of edges $t(n, 2)$ of the Turán graph $T(n, 2)$.

## Background

- [Turán density of complete graphs](../tur-n-density-of-complete-graphs/turan-density-complete-graph.md): the asymptotic form $\pi(K_3) = 1/2$ and its generalisation to $K_{r+1}$.

## Sources

- W. Mantel, Problem 28, Wiskundige Opgaven 10 (1907), 60-61.
