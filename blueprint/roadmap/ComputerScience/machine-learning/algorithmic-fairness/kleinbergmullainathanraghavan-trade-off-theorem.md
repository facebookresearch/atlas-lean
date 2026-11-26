# Kleinberg–Mullainathan–Raghavan trade-off theorem

Consider a finite population partitioned into two nonempty groups, with a finite set $\Sigma$ of occurring
feature vectors. For $t\in\{1,2\}$ let
$a_{t\sigma}\ge0$ be the group-$t$ frequency of feature $\sigma$, with $\sum_\sigma a_{t\sigma}=1$.
Every $\sigma\in\Sigma$ occurs in at least one group. The conditional positive-class probability for feature
$\sigma$ is $p_\sigma\in[0,1]$, the same in both groups wherever that feature occurs. Define the base rates
$\mu_t=\sum_\sigma a_{t\sigma}p_\sigma$ and assume $0<\mu_t<1$, so both classes are nonempty in each group.

A risk assignment maps each feature $\sigma$ to a probability distribution over finitely many score bins in
$[0,1]$, using only $\sigma$ and randomness independent of group and class conditional on $\sigma$. Use one bin
for each distinct score value. Calibration within groups is required on each group/bin cell of positive
probability; balance for each class compares the class-conditional mean scores across the two groups.

If a risk assignment satisfies calibration within groups and balance for both classes, then the instance
allows perfect prediction ($p_\sigma\in\{0,1\}$ for every $\sigma\in\Sigma$) or has equal base rates
$\mu_1=\mu_2$. Conversely, in either of these cases some risk assignment satisfies all three conditions.
This statement uses the nonempty-class convention above; it makes no claim based on an undefined conditional
mean in an empty class.

## Depends on

- [Group fairness criteria for scores and classifiers](group-fairness-criteria-for-scores-and-classifiers.md)

## Sources

- J. Kleinberg, S. Mullainathan and M. Raghavan, *Inherent trade-offs in the fair determination of risk scores*, ITCS 2017; arXiv:1609.05807, §§1.1–2 (population and randomized assignment model), Theorem 1.1 and the discussion of the two special cases in §1. <https://arxiv.org/pdf/1609.05807>
