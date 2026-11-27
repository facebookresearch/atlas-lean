# The Λ-coalescent on the natural numbers

Let $\Lambda$ be a finite measure on $[0, 1]$. There is a process $(\Pi_t)_{t \ge 0}$ with values in the
partitions of $\mathbb N$, unique in law, such that for every $n$ the restriction of $\Pi$ to
$\{1, \dots, n\}$ has the finite-dimensional distributions of the path process with the
[Λ-coalescent rate matrix](../../coalescents/the-coalescent-rate-matrix-on-partitions-of-a-fi.md) $Q^\Lambda_n$ started from singletons. It can be chosen so that
every restriction has right-continuous paths with left limits, and its law is invariant under finite
permutations of $\mathbb N$. This is the Λ-coalescent.

## Depends on

- [The Λ-coalescent rate matrix on partitions of a finite sample](../../coalescents/the-coalescent-rate-matrix-on-partitions-of-a-fi.md)

## Proof depends on

- [Path laws of the Λ-coalescent on a finite sample are consistent under restriction](../../coalescents/path-laws-of-the-coalescent-on-a-finite-sample-a.md)
- [Kolmogorov extension theorem](../../../../Probability/foundations/kolmogorov-extension-theorem/kolmogorov-extension.md)

## Expansion

The construction is the one for [Kingman's coalescent on the natural numbers](../../partition-valued-kingman-coalescent/kingman-coalescent-on-n-as-a-time-indexed-cadlag.md) with the
Λ-coalescent rate matrices in place of Kingman's: Kolmogorov extension over pairs of a sample size and a
rational time, right limits along rational times of the refinement-monotone finite-state restricted paths,
almost sure agreement with the coordinates at all rational times, and the prescribed finite-dimensional
distributions at real times by stochastic continuity of the finite chains, whose rates are bounded.

## Sources

- J. Pitman, "Coalescents with multiple collisions", Annals of Probability 27 (1999), 1870–1902, <https://doi.org/10.1214/aop/1022874819>.
- N. Berestycki, *Recent progress in coalescent theory*, Ensaios Matemáticos 16, Sociedade Brasileira de Matemática (2009), preprint <https://arxiv.org/abs/0909.3985>, Section 3.1, Definitions 3.1 and 3.2 and the sentence between them.
