# Chen's identity

Let the velocity $v$ of a path $X$ in $\mathbb{R}^\iota$ be interval integrable on every
interval. Then for all reals $a, b, c$ and every word $w = i_1 \cdots i_k$,

$$S(X)^{i_1 \cdots i_k}_{a,c} = \sum_{m=0}^{k} S(X)^{i_1 \cdots i_m}_{a,b}\; S(X)^{i_{m+1} \cdots i_k}_{b,c}.$$

Equivalently $S(X)_{a,c} = S(X)_{a,b} \otimes S(X)_{b,c}$ in the algebra of tensor series: the
signature turns concatenation of paths into the tensor product.

The source states it for $a < b < c$; with oriented integrals the same induction on $k$ (split
$\int_a^c = \int_a^b + \int_b^c$ in the last integration and apply the induction hypothesis
inside $\int_b^c$) gives it for all $a, b, c$.

## Sources

- I. Chevyrev and A. Kormilitzin, *A primer on the signature method in machine learning*,
  arXiv:1603.03788v2, Theorem 1.17, equation (19), and Theorem 1.22.
