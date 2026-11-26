# Noiseless recovery, $\ell_2$ error

Let $\iota$ be a finite index set, $s \ge 1$, and $\Phi \in \mathbb{R}^{m \times \iota}$ with the
[restricted isometry property](has-rip.md) of order $2s$ with a constant $\delta < \sqrt{2} - 1$.
Let $x \in \mathbb{R}^\iota$ and let $\hat x$ solve $\min \|\tilde x\|_1$ subject to
$\Phi \tilde x = \Phi x$. Then for every set $S$ of at most $s$ indices,

$$\|\hat x - x\|_2 \le \frac{C_0}{\sqrt{s}} \sum_{j \notin S} |x_j|, \qquad C_0 = \frac{2(1 + \rho)}{1 - \rho}, \quad \rho = \frac{\sqrt{2}\,\delta}{1 - \delta} .$$

Taking for $S$ the support of a best $s$-term approximation $x_s$ of $x$ gives the bound
$C_0 s^{-1/2} \|x - x_s\|_1$ of the source.

## Informally uses

- [Near-orthogonality of disjointly supported sparse vectors](abs-dot-product-mul-vec-le.md): (5) is the case $\varepsilon = 0$ of the proof of Theorem 1.3, which uses Lemma 2.1.

## Sources

- E. J. Candès, *The restricted isometry property and its implications for compressed sensing*, C. R. Acad. Sci. Paris, Ser. I 346 (2008) 589–592, Theorem 1.2, eq. (5)
