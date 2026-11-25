# Expander mixing lemma

Let $G$ be a finite simple graph on $N$ vertices with adjacency matrix $A$, and let $d$ be a natural number and $\lambda$ a real number such that $G$ is a [spectral expander](is-spectral-expander.md) of degree $d$ with parameter $\lambda$: $G$ is $d$-regular, $\lambda \ge 0$ and $\lVert A x\rVert \le d \lambda \lVert x\rVert$ for every $x$ orthogonal to the constant vector, with $d \ge 1$. For all vertex sets $S$ and $T$ of densities $\alpha = \lvert S\rvert/N$ and $\beta = \lvert T\rvert/N$ (quotients by $N = 0$ being read as $0$),

$$\Big\lvert \frac{e(S, T)}{N d} - \alpha\beta \Big\rvert \le \lambda \sqrt{\alpha(1 - \alpha)\, \beta(1 - \beta)},$$

where $e(S, T)$ is the number of ordered pairs $(s, t) \in S \times T$ with $s$ adjacent to $t$ (S. Vadhan, *Pseudorandomness*, Foundations and Trends in Theoretical Computer Science 7 (2012), Lemma 4.15, first inequality).

The proof writes $e(S, T) = 1_S^{\mathsf T} A\, 1_T$, splits each indicator into its mean and a part orthogonal to the constants, and bounds the cross term by the Cauchy–Schwarz inequality and the spectral bound; it uses nothing about $A$ beyond symmetry, constant row sums and the spectral bound, which is the content of the [expander mixing lemma for matrices](abs-indicator-dot-product-mul-vec-sub-le.md). The hypothesis $d \ge 1$ is needed: the empty graph satisfies the spectral bound with $\lambda = 0$, but has no edges between nonempty sets.

## Background

- [Elementary lower bound on the spectral parameter](elementary-spectral-lower-bound.md): $\lambda$ is
  at least about $1/\sqrt d$, so for sparse graphs the error term never vanishes; the lemma is
  informative for sets of density well above $\lambda$.
- [Conductance and Cheeger's inequality](../../algebraic-graph-theory/part-02/conductance-and-cheeger-s-inequality/README.md):
  taking $T$ the complement of $S$ gives edge expansion from spectral expansion, the easy direction
  of Cheeger's inequality.
