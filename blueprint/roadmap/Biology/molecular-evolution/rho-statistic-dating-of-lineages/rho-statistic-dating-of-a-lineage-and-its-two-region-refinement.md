# Rho statistic dating of a lineage and its two-region refinement

**Setting.** A lineage (for example a mitochondrial founder lineage) is sampled $n$ times, and the
sampled sequences are placed on a rooted phylogeny of the lineage with links $1, \dots, k$. On link $i$,
$l_i$ mutations are observed in the genomic region under study and $n_i$ sampled sequences descend
from that link. Mutations occur as a Poisson process at rate $u$ per year in the region, which holds
exactly under simple substitution models (Kimura's three-parameter model or simpler).

**Rho statistic.** The average number of mutations from the root to the samples and its estimated
variance are

$$\rho = \frac{1}{n} \sum_{i=1}^{k} n_i\, l_i, \qquad \widehat{\operatorname{Var}}(\rho) = \frac{1}{n^2} \sum_{i=1}^{k} n_i^2\, l_i,$$

and the time to the most recent common ancestor (TMRCA) of the lineage is estimated by
$\hat{t} = \rho / u$, which is unbiased for the TMRCA under the Poisson model.

**Two-region refinement.** Suppose that $m < n$ of the samples are also typed in a second region
(for example the coding region) with Poisson mutation rate $v$, giving counts $r_1, \dots, r_k$ on links
carrying $m_1, \dots, m_k$ such samples. The second region alone gives the unbiased estimator
$\hat t_2 = \frac{1}{mv} \sum_{i=1}^{k} m_i\, r_i$, and the two are combined into

$$t^{*} = \frac{\sum_{i=1}^{k} n_i\, l_i + \sum_{i=1}^{k} m_i\, r_i}{n u + m v} = \frac{n u\, \hat{t} + m v\, \hat t_2}{n u + m v},$$

the total root-to-tip mutation count over both regions divided by the number of mutations it is expected to accumulate per year of TMRCA. Then:

1. $\operatorname{Var}(t^{*}) < \operatorname{Var}(\hat{t})$ whenever $0 < m \le 2$;
2. if the phylogeny is star-like, $t^{*}$ has the smallest variance among unbiased estimators that
   are convex combinations of the two region-specific estimators.

## Depends on

Its statement uses only the notions recalled above.

## Proof depends on

- [The Rao–Blackwell theorem](../../../Probability/statistical-estimation/rao-blackwell-theorem/rao-blackwell.md)

## Expansion

Each sample's root-to-tip mutation count is Poisson with mean $uT$, so averaging over samples gives
an unbiased estimate of $uT$; samples sharing a link share its mutations, which is why the variance
weights each link's count by $n_i^2$ rather than $n_i$. Under a star phylogeny the branches are
independent and the total mutation count over both regions is a sufficient statistic, so
Rao-Blackwellization makes the optimally weighted combination the best convex combination. A rate
for a typed sub-region can be calibrated against coding-region synonymous transitions on complete
sequences from the same haplogroup. Founder lineages are then those that coalesce within the
historical window of a community, which bounds the minimal number of maternal founders.

## Sources

- D. M. Behar, E. Metspalu, T. Kivisild, S. Rosset, S. Tzur, Y. Hadid, G. Yudkovsky, D. Rosengarten,
  et al., "Counting the founders: the matrilineal genetic ancestry of the Jewish Diaspora", PLoS ONE
  3 (2008) e2062, Materials and Methods, coalescence estimates and Theorem 1,
  <https://doi.org/10.1371/journal.pone.0002062> (PMC2323359).
