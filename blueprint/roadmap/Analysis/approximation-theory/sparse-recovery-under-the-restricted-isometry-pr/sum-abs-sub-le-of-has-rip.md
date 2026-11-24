# Noiseless recovery, $\ell_1$ error

Let $\iota$ be a finite index set, $s \ge 1$, and $\Phi \in \mathbb{R}^{m \times \iota}$ with the
[restricted isometry property](has-rip.md) of order $2s$ with a constant $\delta < \sqrt{2} - 1$.
Let $x \in \mathbb{R}^\iota$ and let $\hat x$ solve $\min \|\tilde x\|_1$ subject to
$\Phi \tilde x = \Phi x$. Then for every set $S$ of at most $s$ indices,

$$\|\hat x - x\|_1 \le C_0 \sum_{j \notin S} |x_j|, \qquad C_0 = \frac{2(1 + \rho)}{1 - \rho}, \quad \rho = \frac{\sqrt{2}\,\delta}{1 - \delta} .$$

Taking for $S$ the support of a best $s$-term approximation $x_s$ of $x$ gives the bound
$C_0 \|x - x_s\|_1$ of the source.

## Informally uses

- [The null-space property under restricted isometry](sum-abs-le-of-mul-vec-eq-zero.md): the source derives (4) from the cone constraint (12) and Lemma 2.2.

## Sources

- E. J. Candès, *The restricted isometry property and its implications for compressed sensing*, C. R. Acad. Sci. Paris, Ser. I 346 (2008) 589–592, Theorem 1.2, eq. (4)
