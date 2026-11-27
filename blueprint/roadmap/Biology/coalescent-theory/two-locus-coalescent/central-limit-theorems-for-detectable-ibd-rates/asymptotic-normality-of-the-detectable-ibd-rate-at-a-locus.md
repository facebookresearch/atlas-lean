# Asymptotic normality of the detectable IBD rate at a locus

Sample $n$ haploid genomes from a Wright–Fisher population of constant size $N$, with time measured in units of $N$ generations, so that for $k \ll N$ the time to the first coalescence among $k$ lineages is approximately exponential with rate $\binom{k}{2}$ (Kingman coalescent). Crossovers form a Poisson process of rate $1$ per Morgan per meiosis, so after $t$ meioses the haplotype segment surviving to the right of a focal point has length $\mathrm{Exponential}(t)$. For haplotypes $a, b$ let $R_{a,b}$ ($L_{a,b}$) be the length of their IBD segment to the right (left) of a fixed locus, and for a detection threshold $w$ Morgans define

$$X_{a,b} = \mathbb{1}\{R_{a,b} \ge w\}, \qquad Y_{a,b} = \mathbb{1}\{L_{a,b} + R_{a,b} \ge w\}.$$

The **detectable IBD rate** is $\bar X = \binom{n}{2}^{-1}\sum_{a<b} X_{a,b}$; its standardized version is

$$\bar Z = \Omega^{-1/2}\sum_{a<b}\big(X_{a,b} - \mathbb{E}X_{a,b}\big), \qquad \Omega = \binom{n}{2}\,\mathbb{E}X_{a,b}\,\big(1 - \mathbb{E}X_{a,b}\big),$$

with $\bar Y$, $\tilde{\bar Z}$ defined analogously. The indicators are identically distributed but dependent through the unobserved genealogy, so the classical i.i.d. central limit theorem does not apply.

**Theorem.** As $n \to \infty$ and $Nw \to \infty$, $\bar Z \Rightarrow N(0,1)$ provided

1. $Nw = o(n^2)$ (many pairs relative to the scaled population size, so many long segments are observed);
2. $n = o(Nw)$ (the sample is small relative to the scaled population size, so covariances between indicators are negligible);
3. $\mathbb{E}\big[Z_{a,b} Z_{-a,b} \mid Z_{-a,b}\big] \ge 0$ for every pair, where $Z_{-a,b}$ is the sum of all other centred indicators.

The same holds for $\tilde{\bar Z}$ (segments overlapping the locus), whose two-, three- and four-haplotype covariances are $O((Nw)^{-1})$, $O((Nw)^{-2})$ and $O((Nw)^{-3})$. If $Nw = C_1 n^{C_2}$ with $1 < C_2 < 2$, the error of the normal approximation is of order $\max(n^{1-C_2}, n^{C_2-2})$, smallest ($n^{-1/2}$) at $C_2 = 3/2$. For $\ell$ disjoint samples of $n$ haplotypes each from the same population (dependent through their shared genealogy), the vector of standardized rates converges to $N_\ell(0, I_\ell)$ under the same conditions, so affine contrasts such as a case–control difference of IBD rates are asymptotically normal.

## Depends on

- [Holding times of Kingman's coalescent](../../kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md)
- [Poisson point process with finite intensity](../../../../Probability/point-processes/poisson-point-processes/poisson-point-process.md)

## Proof depends on

Its proof is that of the source below, as the Expansion describes.

## Expansion

The proof applies a central limit theorem for dependent data that requires the total covariance among the summands to be negligible relative to their total variance. Under the coalescent with recombination, two pairs sharing a haplotype are correlated through the shared lineage and disjoint pairs through the tree, and both covariances shrink in $Nw$ fast enough under condition 2, while condition 1 keeps the variance growing. Condition 3 fails for the pathological $n = 3$ but is supported by simulation for larger samples. In real human data the conditions are hard to meet, so the theorem indicates when a Gaussian approximation to IBD-rate statistics (as in IBD-based selection scans) is reasonable rather than guaranteeing it.

## Sources

- S. D. Temple and E. A. Thompson, "Identity-by-descent segments in large samples", Theoretical Population Biology (2025), Sections 2–4, Eqs. (1)–(11), Theorems 3.1, 3.3 and 4.1–4.3 and Proposition 3.2, <https://doi.org/10.1016/j.tpb.2025.06.003>, PMCID: PMC13308687.
