# Han–Eskin random-effects statistic and m-values

**Setting.** Datasets $i = 1, \dots, T$ report independent effect estimates $\beta_i$ with variances $V_i$ (correlated estimates can first be transformed as in [fixed-effects meta-analysis of correlated estimates](fixed-effects-meta-analysis-of-correlated-effect-estimates.md)).

**Random-effects statistic.** Under $\beta_i \sim \mathcal{N}(\mu, V_i + \tau^2)$, test $H_0: \mu = 0, \tau^2 = 0$ (no effect in any dataset) against $\mu \ne 0$ or $\tau^2 > 0$ by the likelihood ratio

$$S_{\mathrm{RE}} = \sum_i \log\frac{V_i}{V_i + \hat\tau^2} + \sum_i \frac{\beta_i^2}{V_i} - \sum_i \frac{(\beta_i - \hat\mu)^2}{V_i + \hat\tau^2},$$

where $(\hat\mu, \hat\tau^2)$ are maximum-likelihood estimates, computed by iterating

$$\hat\mu = \frac{\sum_i \beta_i/(V_i + \hat\tau^2)}{\sum_i 1/(V_i + \hat\tau^2)}, \qquad \hat\tau^2 = \max\!\left(0, \frac{\sum_i \big[(\beta_i - \hat\mu)^2 - V_i\big]/(V_i + \hat\tau^2)^2}{\sum_i 1/(V_i + \hat\tau^2)^2}\right)$$

from a moment starting value of $\tau^2$. Its $p$-value is read from tables of the null distribution of $S_{\mathrm{RE}}$.

**m-value.** Let $c \in \{0,1\}^T$ indicate which datasets carry an effect, with prior $P(c) = B(|c| + \alpha, T - |c| + \beta)/B(\alpha, \beta)$ ($|c|$ the number of ones, $B$ the beta function, $\alpha = \beta = 1$), and let $P(\beta_1, \dots, \beta_T \mid c)$ model $\beta_i \sim \mathcal{N}(0, V_i)$ for $c_i = 0$ and, for $c_i = 1$, $\beta_i \sim \mathcal{N}(\mu, V_i)$ with a shared effect $\mu \sim \mathcal{N}(0, \sigma^2)$ integrated out. The m-value of dataset $i$ is the posterior probability

$$m_i = P(c_i = 1 \mid \beta) = \frac{\sum_{c:\,c_i = 1} P(\beta \mid c)\, P(c)}{\sum_{c} P(\beta \mid c)\, P(c)} .$$

## Expansion

The traditional random-effects test inflates the variance by $\hat\tau^2$ under the null as well, so it is conservative and never beats the fixed-effects test; the likelihood ratio above instead uses $\tau^2 = 0$ under the null, and gains power when the effect is present in only some datasets or varies in size. Its null law is a mixture because $\tau^2 = 0$ lies on the boundary, hence the tabulated $p$-values. The m-value sums over all $2^T$ configurations (exactly for small $T$, by sampling otherwise); values near $1$ predict that the effect exists in dataset $i$ and values near $0$ that it is absent, a distinction that a per-dataset $p$-value cannot make because a large $p$-value is also produced by low power. In multi-tissue eQTL mapping these two quantities detect eQTLs with heterogeneous effects across tissues and predict the tissues in which each eQTL acts.

## Depends on

- [DerSimonian–Laird random-effects meta-analysis](dersimonian-laird-random-effects-meta-analysis.md)
- [Fixed-effects meta-analysis of correlated effect estimates](fixed-effects-meta-analysis-of-correlated-effect-estimates.md)

## Sources

- J. H. Sul, B. Han, C. Ye, T. Choi and E. Eskin, "Effectively identifying eQTLs from multiple tissues by combining mixed model and meta-analytic approaches", PLoS Genetics 9 (2013), e1003491, Materials and Methods (Equation (6), "Random effects model"; "Predicting effects of eQTLs in multiple tissues"), <https://doi.org/10.1371/journal.pgen.1003491>, PMCID PMC3681686.
- B. Han and E. Eskin, "Random-effects model aimed at discovering associations in meta-analysis of genome-wide association studies", American Journal of Human Genetics 88 (2011), 586–598, <https://doi.org/10.1016/j.ajhg.2011.04.014>.
