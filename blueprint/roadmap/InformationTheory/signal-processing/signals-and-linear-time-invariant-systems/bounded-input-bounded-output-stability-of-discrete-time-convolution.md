# Bounded-input bounded-output stability of discrete-time convolution with a summable kernel

Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, let $E$, $F$ and $G$ be normed spaces over $\mathbb{K}$ with $G$ complete, and let $M : E \times F \to G$ be a continuous bilinear map with norm $\|M\| = \sup\{\|M(e, f)\| : \|e\|, \|f\| \le 1\}$. Let $h : \mathbb{Z} \to E$ satisfy $\|h\|_1 = \sum_{k \in \mathbb{Z}} \|h(k)\| < \infty$, and let $x : \mathbb{Z} \to F$ be bounded, with $\|x\|_\infty = \sup_{n} \|x(n)\|$. Then for every $n \in \mathbb{Z}$ the series

$$y(n) = \sum_{k \in \mathbb{Z}} M\big(h(k), x(n - k)\big)$$

converges absolutely in $G$, and

$$\|y(n)\| \le \|M\|\, \|h\|_1\, \|x\|_\infty .$$

So $x \mapsto y$ is a linear map from bounded sequences in $F$ to bounded sequences in $G$ with operator norm at most $\|M\|\,\|h\|_1$: the discrete-time linear shift-invariant system with kernel $h$ is bounded-input bounded-output stable. The kernel always stands in the first argument of $M$. For matrix kernels, $E = \mathbb{K}^{p \times m}$, $F = \mathbb{K}^m$, $G = \mathbb{K}^p$ and $M(H, v) = Hv$, so $y(n) = \sum_k h(k)\, x(n - k)$ with $\|M\| = 1$ for the operator norm on $E$; for scalar signals, $M$ is multiplication in $\mathbb{K}$.

**Proof.** For each $k$, $\|M(h(k), x(n - k))\| \le \|M\|\, \|h(k)\|\, \|x(n - k)\| \le \|M\|\, \|x\|_\infty\, \|h(k)\|$, and the right side is summable over $k \in \mathbb{Z}$. An absolutely summable family in the complete space $G$ is summable, and the norm of its sum is at most the sum of the norms, which gives both conclusions. Linearity of $x \mapsto y$ follows from linearity of $M$ in its second argument and of summation.

## Background

- [Summability of convolution terms for $\ell^1$ and $\ell^p$ sequences](../../../Analysis/banach-spaces/sequence-spaces/convolution-on-p/summable-int-conv-term.md): the complex scalar case of the absolute convergence, for every $1 \le p \le \infty$
- [Young's inequality with one $\ell^1$ factor](../../../Analysis/banach-spaces/sequence-spaces/convolution-on-p/norm-l1-conv-le.md): the scalar $\ell^1$–$\ell^p$ norm bound, whose case $p = \infty$ is the bound above for $E = F = G = \mathbb{C}$

## Sources

- M. Vetterli, J. Kovačević and V. K. Goyal, *Foundations of Signal Processing*, Cambridge University Press, 2014 (free version v1.1), <https://fourierandwavelets.org/FSP_v1.1_2014.pdf>, Section 3.3, Theorem 3.8 (BIBO stability, pp. 208–209), whose sufficiency proof is the bound $|y_n| \le \|x\|_\infty \|h\|_1$ for scalar sequences. The vector-valued form with a continuous bilinear map and a complete codomain is derived on the page.
