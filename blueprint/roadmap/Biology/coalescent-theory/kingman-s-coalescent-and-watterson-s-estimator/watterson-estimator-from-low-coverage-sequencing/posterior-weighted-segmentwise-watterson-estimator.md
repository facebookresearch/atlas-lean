# Posterior-weighted segmentwise Watterson estimator for low-coverage data

**Setting.** Sequence reads from $N$ haploid (or fully inbred) lines are aligned to a reference window. Partition the window into segments $s = 1, \dots, K$ such that every site of segment $s$ is covered by exactly the same set of $n_s \ge 2$ lines; segment $s$ has $L_s$ sites. For each site $j$ a SNP caller returns $\pi_j \in [0, 1]$, the posterior probability, given the reads $R$, that the site is segregating among the lines covering it. Define

$$\hat S_s = \sum_{j \in s} \pi_j, \qquad a_n = \sum_{i=1}^{n-1} \frac1i, \qquad \hat\theta_s = \frac{\hat S_s}{a_{n_s} L_s}, \qquad \hat\theta = \frac{\sum_s L_s\,\hat\theta_s}{\sum_s L_s} = \frac{\sum_s \hat S_s / a_{n_s}}{\sum_s L_s}.$$

**Proposition (unbiasedness under calibrated posteriors).** Assume (i) neutral infinite-sites mutation at per-site rate $\theta/2$ on a Kingman genealogy of all $N$ lines, so that for the $n_s$ lines covering segment $s$ the true number of segregating sites $S_s$ satisfies $\mathbb E S_s = \theta a_{n_s} L_s$; (ii) the coverage pattern (which lines cover which sites) is independent of the genealogy and the mutations; and (iii) the posteriors are calibrated, $\pi_j = \mathbb P(\text{site } j \text{ segregating} \mid R)$ under the true data-generating model. Then $\mathbb E\,\hat\theta_s = \theta$ for every segment and $\mathbb E\,\hat\theta = \theta$.

**Behavior.** The estimator weights each candidate SNP by the probability that it is real instead of thresholding, and it corrects for variable depth by using the right harmonic constant for each segment. Its variance grows quickly as coverage falls, because segments become short and $n_s$ small. If the posteriors are miscalibrated, replacing $\pi_j$ by $\mathbf 1\{\pi_j \ge c\}$ for a high cutoff $c$ or by $1$ for every observed candidate gives conservative and permissive versions; the permissive version is always at least $\hat\theta$, and the two bracket the effect of a badly wrong error model.

## Depends on

- [Watterson's estimator is unbiased](../watterson-unbiased.md)
- [Infinite-sites mutation on the Kingman genealogy](../../poisson-mutation-on-the-kingman-genealogy/kingman-mutation-kernel.md)

## Proof depends on

- [Path laws of Kingman's coalescent on a finite sample are consistent under restriction](../../partition-valued-kingman-coalescent/strong-path-level-restriction-consistency-of-the.md)

## Expansion

Since $\pi_j = \mathbb E[\mathbf 1\{\text{site } j \text{ segregating}\} \mid R]$, the tower property gives $\mathbb E\,\hat S_s = \mathbb E S_s$. By (ii) one may condition on the coverage pattern, and the $n_s$ lines covering a segment are then a fixed subsample; by sampling consistency of Kingman's coalescent their genealogy is a Kingman genealogy of size $n_s$, so Watterson's identity $\mathbb E S_s = \theta a_{n_s} L_s$ applies and $\mathbb E\,\hat\theta_s = \theta$. The window estimator is a fixed convex combination of the $\hat\theta_s$ given the coverage pattern, hence also unbiased. Haploidy matters: with diploid outbred samples a site covered by one read per individual samples an unknown number of distinct chromosomes, and the sample size $n_s$ is itself uncertain; inbred lines carry one allele per site, which removes that layer. Unbiasedness says nothing about the variance, which also depends on recombination through the correlation of genealogies along the window.

## Sources

- T. B. Sackton, R. J. Kulathinal, C. M. Bergman, A. R. Quinlan, E. B. Dopman, M. Carneiro, G. T. Marth, D. L. Hartl, A. G. Clark, *Population genomic inferences from sparse high-throughput sequencing of two populations of Drosophila melanogaster*, Genome Biology and Evolution (2009), <https://doi.org/10.1093/gbe/evp048>, PMCID PMC2839279. Materials and Methods, "Estimating θ Using Partial Data" (segments of constant depth, segregating sites as a sum of SNP posterior probabilities, Watterson's estimator per segment, length-weighted window average), and Results, "Developing Methods to Infer Patterns of SNP Variation with Short-Read Data" (simulations showing no bias from 0.1x to 4x coverage with rising variance, conservative and permissive worst cases). The unbiasedness proposition and its proof are stated here under explicit calibration and independence assumptions.
