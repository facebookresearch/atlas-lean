# Temporal covariance of allele frequency change and the G(t) statistic

**Setting.** Let $p_t$ be the frequency of an allele in a closed population at generation $t$ and $\Delta p_t = p_{t+1} - p_t$. Across loci genome-wide (or across replicate populations), consider the variances $\operatorname{Var}(\Delta p_t)$ and covariances $\operatorname{Cov}(\Delta p_s, \Delta p_t)$, $s \ne t$, of the allele frequency changes.

**Decomposition.** Since $p_t - p_0 = \sum_{i=0}^{t-1}\Delta p_i$,

$$\operatorname{Var}(p_t - p_0) = \sum_{i=0}^{t-1}\operatorname{Var}(\Delta p_i) + \sum_{i=0}^{t-1}\sum_{j \ne i}\operatorname{Cov}(\Delta p_i, \Delta p_j).$$

**Neutral null.** Under neutral drift alone the frequency process is a martingale, $\mathbb{E}[\Delta p_t \mid p_0, \dots, p_t] = 0$, so $\operatorname{Cov}(\Delta p_s, \Delta p_t) = 0$ for $s \ne t$. Heritable fitness variation makes a neutral allele's changes in different generations covary through its persistent association with selected backgrounds (linked selection).

**The statistic.**

$$G(t) = \frac{\sum_{i=0}^{t-1}\sum_{j \ne i}\operatorname{Cov}(\Delta p_i, \Delta p_j)}{\operatorname{Var}(p_t - p_0)}$$

is the share of the total variance in allele frequency change from generation $0$ to $t$ contributed by temporal covariances. When the covariances are positive it is a lower bound on the fraction of allele frequency change caused by selection, because selection also inflates the per-generation variances, which $G(t)$ attributes to drift. For replicate populations $A \ne B$ under a shared selection pressure, the convergence correlation

$$\operatorname{cor}(\Delta p_s, \Delta p_t) = \frac{\mathbb{E}_{A\ne B}\operatorname{Cov}(\Delta p_{s,A}, \Delta p_{t,B})}{\mathbb{E}_{A\ne B}\sqrt{\operatorname{Var}(\Delta p_{s,A})\operatorname{Var}(\Delta p_{t,B})}}$$

measures the part of the response shared across replicates.

## Remarks

The decomposition is the variance of a sum. The martingale property of neutral Wright–Fisher drift gives uncorrelated increments: for $s < t$, conditioning on the history up to generation $t$ kills $\mathbb{E}[\Delta p_s\Delta p_t]$. In practice covariances are estimated between blocks of generations at the sampling times, corrected for the bias that binomial sampling of reads and individuals adds to the variances and to covariances between adjacent intervals (which share an endpoint), and standardized by heterozygosity; uncertainty comes from a block bootstrap over genomic windows. Covariances between adjacent generations that fall inside one sampling interval do not enter the numerator, which makes $G(t)$ more conservative. Reanalysis of three selection experiments gave lower bounds of about 17–37% of allele frequency change caused by selection, and $G(t)$ grows and then plateaus as older covariances decay. Negative covariances signal reversals in the direction of selection.

## Depends on

- [One-step martingale property of the Wright–Fisher allele count](../../population-genetics/wright-fisher-markov-chain/sum-prob-mul-wright-fisher.md)

## Sources

- V. Buffalo and G. Coop, "Estimating the genome-wide contribution of selection to temporal allele frequency change", Proceedings of the National Academy of Sciences USA 117 (2020), 20672–20680, Results (Equations [1] and [2]) and Materials and Methods, <https://doi.org/10.1073/pnas.1919039117>, PMCID PMC7456072.
