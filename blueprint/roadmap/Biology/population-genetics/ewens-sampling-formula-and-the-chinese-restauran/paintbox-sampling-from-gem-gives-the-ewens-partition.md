# Paintbox sampling from GEM weights gives the Ewens partition

Let $(P_1, P_2, \dots)$ have the GEM($\theta$) distribution, $P_1 = W_1$ and $P_j = W_j\prod_{i<j}(1 - W_i)$ with $W_i$ i.i.d. $\mathrm{Beta}(1, \theta)$, $\theta > 0$; its decreasing rearrangement has the Poisson–Dirichlet distribution PD($\theta$). Given $(P_j)$, let $X_1, \dots, X_n$ be i.i.d. with $P(X_m = j) = P_j$, and let $\Pi_n$ be the partition of $\{1, \dots, n\}$ by equal values. Then $\Pi_n$ has the Ewens($\theta$) law: $P(\Pi_n = \pi) = \frac{\theta^{k}}{\theta(\theta + 1)\cdots(\theta + n - 1)}\prod_{B \in \pi}(|B| - 1)!$ for a partition $\pi$ with $k$ blocks, which is also the law of the Chinese restaurant process with parameter $\theta$ (Berestycki 2009, Definition 1.3 and Theorem 1.5, which identify the paintbox partition of the stick-breaking frequencies with the Chinese restaurant process, and Theorem 1.6 for this partition formula). The allele-count form, that the allele counts of a sample drawn from PD($\theta$) frequencies follow the Ewens sampling formula, is the one-class case $k = 1$ of the mixture representation on [Refined Ewens sampling formula for multiple mutation classes](multi-class-ewens-sampling-formula/refined-ewens-sampling-formula-for-multiple-mutation-classes.md) and is not restated here; this page states the partition-level law for GEM($\theta$) weights and its identification with the Chinese restaurant law. The stick-breaking definition of GEM($\theta$) is separate from this sampling theorem.

## Depends on

- [Stick-breaking weights](../../../Probability/bayesian-statistics/dirichlet-process/stick-weight.md)
- [Chinese restaurant process](../../../Probability/bayesian-statistics/blackwell-macqueen-urn/crp.md)
- [Closed-form law of the Chinese restaurant process](../../../Probability/bayesian-statistics/blackwell-macqueen-urn/crp-prob.md)

## Proof depends on

- [Ewens sampling formula](../../../Biology/population-genetics/ewens-sampling-formula-and-the-chinese-restauran/ewens-prob.md)
- [The allelic partition of the Chinese restaurant process follows the Ewens sampling formula](../../../Biology/population-genetics/ewens-sampling-formula-and-the-chinese-restauran/crp-map-block-sizes.md)

## Expansion

1. The GEM($\theta$) and PD($\theta$) distributions, and the size-biased permutation relating them.
2. The [Ewens sampling formula](../../../Biology/population-genetics/ewens-sampling-formula-and-the-chinese-restauran/ewens-prob.md) and the [Chinese restaurant process and Hoppe's urn](../../../Biology/population-genetics/ewens-sampling-formula-and-the-chinese-restauran/crp-map-block-sizes.md).
3. The computation of $P(\Pi_n = \pi)$ given GEM weights, by conditioning on the order of first appearance and Beta integrals.
4. The equality with the Chinese restaurant law.

## Sources

- N. Berestycki, *Recent Progress in Coalescent Theory*, Ensaios Matemáticos 16, Sociedade Brasileira de Matemática, 2009. <https://arxiv.org/abs/0909.3985>
