# Annotation-informed spike-and-slab priors for polygenic risk prediction

**Setting.** With standardized phenotype and genotypes and $Y = X\beta + \varepsilon$, let $S_0, S_1, \dots, S_K$ be functional annotation categories ($S_0$ the whole genome) and suppose, as in stratified LD-score regression, that per-SNP heritability is additive over overlapping annotations: $\mathrm{Var}(\beta_i) = \sum_{j : i \in S_j} \tau_j$, with $\hat\tau_j$ estimated from GWAS summary statistics. Let $p_0 \in (0,1]$ be the overall proportion of causal SNPs (a tuning parameter) and $\hat H^2$ a summary-statistic estimate of chip heritability (an approximation to the Haseman–Elston estimator computed from the mean of $N\hat\beta_i^2$ and the mean LD score).

**Definition (two priors).**

1. *Annotation-scaled effect sizes, common causal proportion.*

$$\beta_i \sim p_0\, \mathcal{N}\!\Big(0, \frac{\hat\sigma_i^2}{p_0}\Big) + (1 - p_0)\,\delta_0, \qquad \hat\sigma_i^2 = c \sum_{j : i \in S_j} \hat\tau_j,$$

with $c > 0$ chosen so that $\sum_i \hat\sigma_i^2 = \hat H^2$. The estimates $\hat\tau_j$ can be negative, so this prior is defined only when $\sum_i \sum_{j : i \in S_j} \hat\tau_j > 0$ and $\hat\sigma_i^2 \ge 0$ for every $i$.
2. *Common effect size, annotation-dependent causal proportion.* Let $T_i$ be the set of SNPs with exactly the same annotation membership as SNP $i$ and $M_{T_i} = |T_i|$. With $M_0$ SNPs in total and causal-effect variance $V$, so that $H_0^2 = p_0 M_0 V$,

$$\beta_i \sim p_{T_i}\, \mathcal{N}(0, V) + (1 - p_{T_i})\,\delta_0, \qquad V = \frac{H_0^2}{p_0 M_0}, \qquad p_{T_i} = \frac{p_0\, M_0\, H_{T_i}^2}{M_{T_i}\, H_0^2},$$

where the heritability of $T_i$ is estimated by apportioning $\hat H^2$ in proportion to the per-SNP estimates,

$$\hat H_{T_i}^2 = \frac{\sum_{k \in T_i} \sum_{j : k \in S_j} \hat\tau_j}{\sum_{k=1}^{M_0} \sum_{j : k \in S_j} \hat\tau_j}\, \hat H^2 .$$

This prior is defined only when $0 \le p_{T_i} \le 1$ for every $i$, that is, $0 \le H_{T_i}^2 \le M_{T_i} H_0^2 / (p_0 M_0)$.

**Properties.**

1. Under prior 1 the prior variance of $\beta_i$ is $\hat\sigma_i^2$, so the total prior variance equals $\hat H^2$; under prior 2 the expected heritability of $T_i$ is $p_{T_i} M_{T_i} V = H_{T_i}^2$.
2. Rescaling by $c$ adapts per-SNP heritabilities estimated with all reference SNPs to the much smaller set of SNPs used for prediction.
3. Both priors reduce to the point-normal prior of LDpred when all $\hat\tau_j$, $j \ge 1$, vanish.

## Depends on

- [Random-effects model of stratified LD-score regression](../stratified-ld-score-regression/model.md)

## Expansion

Under prior 1, $\mathrm{Var}(\beta_i) = p_0 \cdot \hat\sigma_i^2/p_0 = \hat\sigma_i^2$, and summing gives $\hat H^2$ by the choice of $c$. Under prior 2, $\mathbb{E}[\#\text{causal in } T_i] = p_{T_i}M_{T_i}$ and each causal SNP contributes $V$, so the expected heritability of $T_i$ is $p_{T_i}M_{T_i}V = p_0 M_0 V\, H_{T_i}^2/H_0^2 = H_{T_i}^2$. When no annotation is informative, $\hat\sigma_i^2$ is constant and $p_{T_i} = p_0$, recovering a single spike-and-slab. Either prior is combined with the block-conditional likelihood of the marginal effects, and posterior means are computed by Gibbs sampling within LD blocks; $p_0$ and the choice of prior are tuned on held-out data. Annotations that concentrate heritability (conserved or tissue-specific functional regions) increase prediction accuracy across several complex diseases relative to annotation-agnostic priors.

## Sources

- Hu Y, Lu Q, Powles R, Yao X, Yang C, Fang F, Xu X, Zhao H, "Leveraging functional annotations in genetic risk prediction for human complex diseases" (2017), Methods, "Heritability partition" and "Empirical prior of effect size", <https://doi.org/10.1371/journal.pcbi.1005589>, PMCID PMC5481142.
