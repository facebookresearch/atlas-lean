# Hausdorff measure of dimension d

Let $X$ be an extended metric space, such as a metric space, with its Borel σ-algebra, and let $d$ be a real number. The
$d$-dimensional Hausdorff measure of a set $A \subseteq X$ is

$$\mathcal{H}^d(A) = \sup_{r > 0} \, \inf\Big\{ \sum_n (\operatorname{diam} t_n)^d : A \subseteq \bigcup_n t_n,\ \operatorname{diam} t_n \le r
\text{ for all } n \Big\},$$

the infimum running over countable covers of $A$, where an empty $t_n$ contributes $0$ and diameters and powers are
computed in $[0, \infty]$, so that $0^0 = 1$. It is a measure on the Borel sets. This is the general form of the
$p$-dimensional Hausdorff measure $H_p$ of a metric space, $p \ge 0$, which takes covers by sets of diameter less than
$\delta$ and lets $\delta \to 0^+$: covers by sets of diameter at most $r$ give the same supremum.

## Idea

For $d = 0$ the Hausdorff measure is counting measure, for $d = 1$ it gives the length of a simple rectifiable curve,
and on $\mathbb{R}^n$ the $n$-dimensional Hausdorff measure is a constant multiple of Lebesgue measure. For a fixed
nonempty set $A$, $\mathcal{H}^d(A)$ is $\infty$ for $d$ below a threshold and $0$ for $d$ above it; the threshold is
the Hausdorff dimension of $A$, for instance $\log 2/\log 3$ for the Cantor set. Restricting to covers by small sets is
what makes $\mathcal{H}^d$ a metric outer measure, hence a measure on the Borel sets.

## Statements

- [Hausdorff measure](hausdorff-measure.md)

## Background

- [Metric outer measures](../metric-outer-measure/README.md): the construction
- [Borel sets are measurable for a metric outer measure](../borel-sets-and-metric-outer-measures/README.md): why it is a Borel measure
