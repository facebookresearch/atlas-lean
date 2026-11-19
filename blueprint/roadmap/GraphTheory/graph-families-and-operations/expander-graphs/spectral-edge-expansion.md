# Spectral expanders have edge expansion, from the mixing lemma

Let $G$ be a finite simple graph on $N$ vertices with adjacency matrix $A$, and let $d$ be a natural number and $\lambda$ a real number such that $G$ is a [spectral expander](is-spectral-expander.md) of degree $d$ with parameter $\lambda$: $G$ is $d$-regular, $\lambda \ge 0$ and $\lVert A x\rVert \le d \lambda \lVert x\rVert$ for every $x$ orthogonal to the constant vector. For every vertex set $S$, the number $e(S, V \setminus S)$ of edges leaving $S$ satisfies

$$d(1 - \lambda)\, \lvert S\rvert\, \lvert V \setminus S\rvert \le N\, e(S, V \setminus S).$$

This is the expander mixing lemma with $T = V \setminus S$ (S. Vadhan, *Pseudorandomness* (2012), remark after Lemma 4.15: Part 1 of Theorem 4.14 follows by setting $T = S^c$).

## Background

- [Expander mixing lemma for matrices](abs-indicator-dot-product-mul-vec-sub-le.md): applied with
  $T = V \setminus S$, where the two square-root factors multiply to $\lvert S\rvert\, \lvert V \setminus S\rvert / N$.
