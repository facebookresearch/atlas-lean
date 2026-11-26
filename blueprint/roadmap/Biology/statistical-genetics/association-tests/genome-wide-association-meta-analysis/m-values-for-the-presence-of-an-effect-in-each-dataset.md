# m-values for the presence of an effect in each dataset

**Setting.** Datasets $i = 1, \dots, T$ report independent effect estimates $\beta_i$ with variances $V_i$ (for correlated estimates whose inverse covariance has positive row sums, the working variances of [fixed-effects meta-analysis of correlated estimates](fixed-effects-meta-analysis-of-correlated-effect-estimates.md) can be substituted, but the estimates stay correlated, so the resulting m-values are approximations, not exact posterior probabilities).

These datasets are first screened for an effect present in any of them with the [Han–Eskin random-effects statistic](han-eskin-random-effects-meta-analysis.md) (with $X_i = \beta_i$ and $C = T$).

**m-value.** Let $c \in \{0,1\}^T$ indicate which datasets carry an effect, with prior $P(c) = B(|c| + \alpha, T - |c| + \beta)/B(\alpha, \beta)$ ($|c|$ the number of ones, $B$ the beta function, $\alpha = \beta = 1$), and let $P(\beta_1, \dots, \beta_T \mid c)$ model $\beta_i \sim \mathcal{N}(0, V_i)$ for $c_i = 0$ and, for $c_i = 1$, $\beta_i \sim \mathcal{N}(\mu, V_i)$ with a shared effect $\mu \sim \mathcal{N}(0, \sigma^2)$ integrated out. The m-value of dataset $i$ is the posterior probability

$$m_i = P(c_i = 1 \mid \beta) = \frac{\sum_{c:\,c_i = 1} P(\beta \mid c)\, P(c)}{\sum_{c} P(\beta \mid c)\, P(c)} .$$

## Remarks

The m-value sums over all $2^T$ configurations (exactly for small $T$, by sampling otherwise); values near $1$ predict that the effect exists in dataset $i$ and values near $0$ that it is absent, a distinction that a per-dataset $p$-value cannot make because a large $p$-value is also produced by low power. In multi-tissue eQTL mapping the random-effects statistic detects eQTLs with heterogeneous effects across tissues, and the m-values predict the tissues in which each eQTL acts.

## Depends on

- [Han–Eskin random-effects meta-analysis](han-eskin-random-effects-meta-analysis.md)
- [Fixed-effects meta-analysis of correlated effect estimates](fixed-effects-meta-analysis-of-correlated-effect-estimates.md)

## Sources

- J. H. Sul, B. Han, C. Ye, T. Choi and E. Eskin, "Effectively identifying eQTLs from multiple tissues by combining mixed model and meta-analytic approaches", PLoS Genetics 9 (2013), e1003491, Materials and Methods ("Predicting effects of eQTLs in multiple tissues"; Equation (6), "Random effects model", for the screening statistic), <https://doi.org/10.1371/journal.pgen.1003491>, PMCID PMC3681686.
- B. Han and E. Eskin, "Random-effects model aimed at discovering associations in meta-analysis of genome-wide association studies", American Journal of Human Genetics 88 (2011), 586–598, <https://doi.org/10.1016/j.ajhg.2011.04.014>.
