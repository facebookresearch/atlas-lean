# Minkowski's inequality

Let $\mu$ be a measure on a set $X$ with a σ-algebra and let $1 \le p \le \infty$. For all functions $f, g$ on $X$ with
values in $\mathbb{R}$, $\mathbb{C}$, a normed space or, more generally, a topological additive monoid with an extended
seminorm in which addition is continuous, such as $[0, \infty]$,

$$\|f + g\|_p \le \|f\|_p + \|g\|_p$$

in $[0, \infty]$, where $\|h\|_p = \big(\int_X \|h\|^p \, d\mu\big)^{1/p}$ for $p < \infty$, $\|h\|_\infty$ is the
essential supremum of $\|h\|$, and $\|h\|_p = \infty$ when $h$ is not almost everywhere strongly measurable. This is the
general form of Minkowski's inequality: for measurable $f, g \colon X \to \mathbb{C}$ and $1 \le p < \infty$ it reads
$\big(\int_X |f + g|^p \, d\mu\big)^{1/p} \le \big(\int_X |f|^p \, d\mu\big)^{1/p} + \big(\int_X |g|^p \, d\mu\big)^{1/p}$.

## Idea

If $f$ or $g$ is not almost everywhere strongly measurable, the right side is $\infty$. Otherwise, for $p = 1$ and
$p = \infty$ the inequality follows from $\|f + g\| \le \|f\| + \|g\|$ pointwise. For $1 < p < \infty$, bound
$\|f + g\|^p$ by $\|f\| \, \|f + g\|^{p-1} + \|g\| \, \|f + g\|^{p-1}$ and apply Hölder's inequality with exponents $p$
and $p/(p-1)$ to each term; dividing by $\|f + g\|_p^{p-1}$, which is finite when $\|f\|_p$ and $\|g\|_p$ are because
$\|f + g\|^p \le 2^{p-1}(\|f\|^p + \|g\|^p)$, and may be taken nonzero, gives the result. This makes $L^p$ a normed
space for $p \ge 1$, for values in a normed space. The inequality fails for $0 < p < 1$: for disjoint sets $A$ and $B$
of measure $1$, $\|1_A + 1_B\|_p = 2^{1/p} > 2$.

## Statements

- [Triangle inequality for the $L^p$ seminorm](e-lp-norm-add-le.md)

## Background

- [L^p spaces](../normed-and-ordered-structure-of-lp-spaces/lp-space-of-a-measure/README.md): the $L^p$ seminorm
- [Hölder's inequality](../h-lder-and-minkowski-inequalities-for-integrals/h-lder-s-inequality/README.md): used in the proof

## Sources

- S. Axler, *Measure, Integration & Real Analysis*, result 7.14 (version read: the open-access PDF dated 12 June 2026).
