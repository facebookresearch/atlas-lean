# Independent sets in spectral expanders are small

Let $G$ be a finite simple graph on $N$ vertices with adjacency matrix $A$, and let $d$ be a natural number and $\lambda$ a real number such that $G$ is a [spectral expander](is-spectral-expander.md) of degree $d$ with parameter $\lambda$: $G$ is $d$-regular, $\lambda \ge 0$ and $\lVert A x\rVert \le d \lambda \lVert x\rVert$ for every $x$ orthogonal to the constant vector, with $d \ge 1$. Then every independent set $S$ of $G$ satisfies

$$(1 + \lambda)\, \lvert S\rvert \le \lambda N,$$

that is $\lvert S\rvert \le \frac{\lambda}{1 + \lambda} N$; so the independence number is at most $\frac{\lambda}{1 + \lambda} N$ (S. Vadhan, *Pseudorandomness* (2012), Problem 4.2 (1)). The proof applies the expander mixing lemma with $T = S$: there are no edges inside $S$, so $d\lvert S\rvert^2/N \le d\lambda \lvert S\rvert(1 - \lvert S\rvert/N)$.

## Background

- [Expander mixing lemma for matrices](abs-indicator-dot-product-mul-vec-sub-le.md): applied with
  $T = S$; an independent set spans no edges, while the lemma forces about $d \lvert S\rvert^2/N$ of them.
