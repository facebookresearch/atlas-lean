# Noisy recovery

Let $\iota$ be a finite index set, $s \ge 1$, and $\Phi \in \mathbb{R}^{m \times \iota}$ with the
[restricted isometry property](has-rip.md) of order $2s$ with a constant $\delta < \sqrt{2} - 1$.
Observe $y = \Phi x + z$ with $\|z\|_2 \le \varepsilon$, and let $\hat x$ solve $\min \|\tilde x\|_1$
subject to $\|y - \Phi \tilde x\|_2 \le \varepsilon$ (problem (7)). Then for every set $S$ of at
most $s$ indices,

$$\|\hat x - x\|_2 \le \frac{C_0}{\sqrt{s}} \sum_{j \notin S} |x_j| + C_1 \varepsilon,$$

with $\rho = \sqrt{2}\,\delta / (1 - \delta)$, $\alpha = 2\sqrt{1 + \delta} / (1 - \delta)$,
$C_0 = 2(1 + \rho)/(1 - \rho)$ and $C_1 = 2\alpha / (1 - \rho)$. For nonempty $\iota$ the restricted
isometry property forces $\delta \ge 0$ ([nonnegativity](nonneg.md)), so these constants are well
defined. For empty $\iota$ every vector is $0$, the restricted isometry property holds for every
$\delta$, and the statement is trivial, with $\sqrt{1 + \delta}$ read as $0$ when $1 + \delta < 0$. Taking for $S$ the support of a best
$s$-term approximation $x_s$ of $x$ gives the bound $C_0 s^{-1/2} \|x - x_s\|_1 + C_1 \varepsilon$ of
the source.

## Informally uses

- [Near-orthogonality of disjointly supported sparse vectors](abs-dot-product-mul-vec-le.md): Lemma 2.1 bounds the cross terms between the blocks $h_{T_j}$ of the error vector.

## Sources

- E. J. Candès, *The restricted isometry property and its implications for compressed sensing*, C. R. Acad. Sci. Paris, Ser. I 346 (2008) 589–592, Theorem 1.3, eq. (8)
