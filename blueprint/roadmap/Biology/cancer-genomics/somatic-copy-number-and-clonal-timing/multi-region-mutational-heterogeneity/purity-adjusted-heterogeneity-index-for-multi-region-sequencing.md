# Purity-adjusted heterogeneity index for multi-region sequencing

Let $g$ mutated genes be sequenced in $b \ge 2$ samples of one tumour. In sample $j$, gene $i$ has
$x_{ij}$ variant reads out of coverage $n_{ij}$, modelled as $X_{ij} \sim \mathrm{Bin}(n_{ij}, \mathrm{VAF}_{ij})$, with maximum-likelihood estimate $\widehat{\mathrm{VAF}}_{ij} = x_{ij}/n_{ij}$.
The one-sided upper 95% confidence limit is the largest allele frequency still compatible with
seeing so few reads,

$$\mathrm{CI}_{ij} = \sup\{\, v \in [0,1] : F(x_{ij};\, n_{ij}, v) \ge 0.05 \,\},$$

where $F(\cdot\,; n, v)$ is the binomial distribution function. Let $T_j$ be the tumour cell
fraction of sample $j$, estimated by the mean VAF in that sample. The purity-adjusted distance of
gene $i$ between samples $j$ and $k$ is

$$D_{ijk} = \min\!\left( \left|\frac{\widehat{\mathrm{VAF}}_{ij}}{T_j} - \frac{\widehat{\mathrm{VAF}}_{ik}}{T_k}\right|,\
\left|\frac{\mathrm{CI}_{ij}}{T_j} - \frac{\widehat{\mathrm{VAF}}_{ik}}{T_k}\right|,\
\left|\frac{\widehat{\mathrm{VAF}}_{ij}}{T_j} - \frac{\mathrm{CI}_{ik}}{T_k}\right| \right),$$

and the heterogeneity index is the mean over genes and unordered sample pairs,

$$\mathrm{HET} = \frac{\sum_{i}\sum_{j}\sum_{k<j} D_{ijk}}{g\, b(b-1)/2}.$$

$\mathrm{HET} = 0$ when all samples are concordant. A mutation with $x_{ij} = 0$ is called absent
only if $\mathrm{CI}_{ij} < 5\%$, and indeterminate otherwise.

## Expansion

At finite depth a subclonal mutation can be missed entirely, so a zero count is evidence of absence
only when the upper confidence limit is small; using the confidence limit in $D_{ijk}$ when it is
closer to the other sample's value prevents sampling noise from being counted as heterogeneity.
A sample with lower tumour content scales every VAF down by $T_j$, so VAFs are compared after
division by $T_j$. With fully clonal heterozygous mutations at purity-adjusted frequency one, a
single extra clonal mutation in one sample contributes distances of order one, which calibrates the
scale. In the source the index correlates negatively with the branching time estimated from
whole-genome data: tumours whose regions diverged late are more heterogeneous between regions.

## Sources

- L. R. Yates, M. Gerstung, S. Knappskog, C. Desmedt, G. Gundem, P. Van Loo, T. Aas,
  L. B. Alexandrov, D. Larsimont, H. Davies, et al., "Subclonal diversification of primary breast
  cancer revealed by multiregion sequencing", Nature Medicine 21 (2015) 751-759, Online Methods,
  "Measuring heterogeneity in targeted capture data", parts (i)-(iii),
  <https://doi.org/10.1038/nm.3886> (PMC4500826).
