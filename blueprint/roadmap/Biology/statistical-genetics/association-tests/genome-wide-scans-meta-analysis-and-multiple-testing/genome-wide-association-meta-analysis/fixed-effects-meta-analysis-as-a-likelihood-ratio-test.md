# Fixed-effects meta-analysis as a likelihood-ratio test

Let $X_1,\dots,X_C$ be effect-size estimates (log odds ratios or regression coefficients) of one variant from $C$ independent studies, with $X_i\sim\mathcal N(\mu,V_i)$, known variances $V_i$ and weights $W_i=V_i^{-1}$. The inverse-variance-weighted estimate and statistic are

$$\bar X=\frac{\sum_iW_iX_i}{\sum_iW_i},\qquad \operatorname{SE}(\bar X)=\Big(\sum_iW_i\Big)^{-1/2},\qquad Z_{FE}=\frac{\bar X}{\operatorname{SE}(\bar X)}=\frac{\sum_iW_iX_i}{\sqrt{\sum_iW_i}},$$

with $Z_{FE}\sim\mathcal N(0,1)$ under $H_0:\mu=0$. The likelihood-ratio statistic for $H_0:\mu=0$ against $\mu\ne0$ in this model equals

$$-2\log\lambda=\sum_i\frac{X_i^2}{V_i}-\sum_i\frac{(X_i-\bar X)^2}{V_i}=Z_{FE}^2 .$$

Likewise, the conventional random-effects test, which first estimates the between-study variance $\hat\tau^2$ and then uses $\bar X^\ast=\sum_i(V_i+\hat\tau^2)^{-1}X_i/\sum_i(V_i+\hat\tau^2)^{-1}$ and $Z_{RE}=\bar X^\ast/\operatorname{SE}(\bar X^\ast)$ with $\operatorname{SE}(\bar X^\ast)=(\sum_i(V_i+\hat\tau^2)^{-1})^{-1/2}$, is the likelihood-ratio test of $\mu=0$ when the same $\hat\tau^2$ is assumed under both hypotheses: $-2\log\lambda=Z_{RE}^2$. In particular, if all $V_i$ are equal then $\bar X^\ast=\bar X$ and $\operatorname{SE}(\bar X^\ast)\ge\operatorname{SE}(\bar X)$, so $Z_{RE}^2\le Z_{FE}^2$ and $p_{RE}\ge p_{FE}$. Without equal variances this ordering can fail.

## Proof sketch

The maximum-likelihood estimate of $\mu$ under the alternative solves $\sum_iW_i(X_i-\mu)=0$, giving $\bar X$; substituting it, $-2\log\lambda=\sum_i(2X_i\bar X-\bar X^2)W_i=\bar X\sum_iW_iX_i=Z_{FE}^2$. The random-effects case is identical with $V_i$ replaced by $V_i+\hat\tau^2$. The second identity exposes why the conventional random-effects test is conservative for discovery: it assumes the heterogeneity estimated under the alternative also exists under the null, although with no genetic effect there can be no heterogeneity of effects. With equal variances the random-effects $p$-value can never be more significant than the fixed-effects one ([equal sampling variances](../../../../../Probability/not-yet-classified/part-17/der-simonian-laird/equal-variances.md)). With unequal variances it can: for $X=(1,-4)$ and $V=(1,4)$, $Z_{FE}=0$, while the DerSimonian–Laird estimate $\hat\tau^2=10$ gives $Z_{RE}\ne0$. Beyond the equal-variance case, the source reports the fixed-effects test as more powerful only as an observation from simulations, not as a general ordering.

## Depends on

- [Inverse-variance weights](../../../../../Probability/hypothesis-testing/meta-analysis/inverse-variance-weights.md)

## Proof depends on

- [Equal sampling variances](../../../../../Probability/not-yet-classified/part-17/der-simonian-laird/equal-variances.md)

## Sources

- B. Han, E. Eskin, "Random-effects model aimed at discovering associations in meta-analysis of genome-wide association studies", Am. J. Hum. Genet. 88 (2011) 586–598, Material and Methods ("FE Approach", "RE Approach", "RE Assumes Heterogeneity under the Null Hypothesis"), Equations (3)–(5), <https://doi.org/10.1016/j.ajhg.2011.04.014>, PMCID PMC3146723.
