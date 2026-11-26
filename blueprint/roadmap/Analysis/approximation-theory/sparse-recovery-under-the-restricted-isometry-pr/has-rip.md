# The restricted isometry property of order $s$ with constant $\delta$

Let $\iota$ be a finite index set, $\Phi \in \mathbb{R}^{m \times \iota}$, $s \in \mathbb{N}$ and
$\delta \in \mathbb{R}$. The matrix $\Phi$ has the restricted isometry property of order $s$ with
constant $\delta$ if every $x \in \mathbb{R}^\iota$ with at most $s$ nonzero entries satisfies

$$(1 - \delta) \|x\|_2^2 \le \|\Phi x\|_2^2 \le (1 + \delta) \|x\|_2^2 .$$

Candès's isometry constant $\delta_s$ is the least such $\delta$. The set of admissible $\delta$ is an
up-set ([monotonicity](mono.md)), nonempty, closed (an intersection of closed half-lines) and, for
$s \ge 1$ and nonempty $\iota$, bounded below by $0$ ([nonnegativity](nonneg.md)), so it has a least
element, and "$\delta_s < c$" means that the property holds for some $\delta < c$; the statements of
this topic use that form. The norms are squared, unlike the [restricted isometry property for
low-rank matrices](../low-rank-matrix-recovery/is-restricted-isometry.md) of Recht, Fazel and
Parrilo, which bounds unsquared norms; the two constants are therefore not interchangeable.

## Sources

- E. J. Candès, *The restricted isometry property and its implications for compressed sensing*, C. R. Acad. Sci. Paris, Ser. I 346 (2008) 589–592, Definition 1.1
