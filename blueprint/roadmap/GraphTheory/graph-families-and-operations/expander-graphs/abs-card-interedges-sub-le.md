# Expander mixing lemma, unnormalised form

Let $G$ be a finite simple graph on $N$ vertices with adjacency matrix $A$, and let $d$ be a natural number and $\lambda$ a real number such that $G$ is a [spectral expander](is-spectral-expander.md) of degree $d$ with parameter $\lambda$: $G$ is $d$-regular, $\lambda \ge 0$ and $\lVert A x\rVert \le d \lambda \lVert x\rVert$ for every $x$ orthogonal to the constant vector. For all vertex sets $S$ and $T$,

$$\Big\lvert e(S, T) - \frac{d\, \lvert S\rvert\, \lvert T\rvert}{N} \Big\rvert \le d \lambda \sqrt{\lvert S\rvert\, \lvert T\rvert},$$

where $e(S, T)$ is the number of ordered pairs $(s, t) \in S \times T$ with $s$ adjacent to $t$, and the quotient is read as $0$ when $N = 0$. This is the weaker second inequality of S. Vadhan, *Pseudorandomness* (2012), Lemma 4.15 ($\ldots \le \lambda\sqrt{\alpha\beta}$), multiplied by $N d$.
