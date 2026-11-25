# Hausdorff measure

Let $X$ be an extended metric space with its Borel σ-algebra and let $d \in \mathbb{R}$. The
$d$-dimensional Hausdorff measure $\mu_H^d$ on $X$ is the measure given by the metric outer measure construction with
the function $r \mapsto r^d$: for every set $A \subseteq X$,

$$\mu_H^d(A) = \sup_{r > 0} \, \inf\Big\{ \sum_n c(t_n) : A \subseteq \bigcup_n t_n,\ \operatorname{diam} t_n \le r
\text{ for all } n \Big\},$$

where the infimum runs over sequences $(t_n)$ of subsets of $X$, $c(t) = (\operatorname{diam} t)^d$ for a nonempty
set $t$, $c(\emptyset) = 0$, and diameters and powers are computed in $[0, \infty]$.
