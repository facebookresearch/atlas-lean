# Expansion of the logarithmic derivative of the k-th derivative (Lemma 6, zeros case)

Let $F$ be a function in the Selberg class with Dirichlet coefficients $a(n)$, write $F^{(k)}$ for
the $k$-th derivative of $F$, let $k \ge 1$, and let $\ell \ge 2$ be such that $a(\ell) \ne 0$
and $a(n) = 0$ for $2 \le n < \ell$. Then there is a real number $E$ such that for every
$s \in \mathbb{C}$ with $\operatorname{Re} s \ge E$,

$$\frac{F^{(k+1)}(s)}{F^{(k)}(s)} = \sum_{l \ge 0} \sum_{n_0, \dots, n_l}
\left(\frac{-1}{a(\ell) (\log \ell)^k}\right)^{l+1} (\log n_0)^{k+1} (\log n_1 \cdots \log n_l)^k
\frac{\ell^{(l+1)s} a(n_0) \cdots a(n_l)}{(n_0 \cdots n_l)^s},$$

where the inner sum runs over the natural numbers $n_0 \ge \ell$ and $n_1, \dots, n_l \ge \ell + 1$,
and the sum over all pairs of $l$ and $(n_0, \dots, n_l)$ converges absolutely.

## Sources

- M. P. Chaudhary, Salem Guiben, Kamel Mazhouda and Mohammed Mekkaoui, *On the a-Points of the kth Derivative of an L-Function in the Selberg Class*, INTEGERS 24 (2024), Article A11, Lemma 6.
