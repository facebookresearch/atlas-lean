# RIVER latent regulatory-status model

**Expression outliers.** For each tissue, log-transformed expression of gene $g$ is regressed on hidden factors, genotype principal components and sex, and the standardized residuals give per-individual $Z$-scores. An individual is the multi-tissue outlier for $g$ if its median $Z$-score across tissues has the largest absolute value among individuals and that absolute value is at least $2$; the outlier indicator for an individual–gene instance is $E \in \{0,1\}$.

**Model.** For instances $n = 1,\dots,N$ (individual–gene pairs) let $G_n \in \mathbb R^P$ collect annotations of the rare variants near the gene and let $\mathrm{FR}_n \in \{0,1\}$ be the unobserved functional regulatory status of those variants. RIVER is the three-layer model

$$\mathrm{FR}_n \mid G_n \sim \mathrm{Bernoulli}\bigl(\operatorname{logit}^{-1}(\beta^\top G_n)\bigr), \qquad E_n \mid \mathrm{FR}_n = s \sim \mathrm{Bernoulli}(\theta_{s}),$$

with priors $\beta_i \sim N(0, 1/\lambda)$ and $\theta_s \sim \mathrm{Beta}(C, C)$, so that $E_n$ is independent of $G_n$ given $\mathrm{FR}_n$.

**EM fit.** The marginal log-likelihood $\sum_n \log\sum_{s\in\{0,1\}} P(E_n, \mathrm{FR}_n = s \mid G_n, \beta, \theta)$ is non-convex and is maximized by expectation–maximization:
- E-step: $\omega_{1n} = \dfrac{P(\mathrm{FR}_n = 1 \mid G_n,\beta)\,P(E_n \mid \mathrm{FR}_n = 1,\theta)}{\sum_{s} P(\mathrm{FR}_n = s \mid G_n,\beta)\,P(E_n \mid \mathrm{FR}_n = s,\theta)}$, $\omega_{0n} = 1 - \omega_{1n}$;
- M-step for $\beta$: maximize $\sum_n\sum_s \omega_{sn}\log P(\mathrm{FR}_n = s \mid G_n, \beta) - \tfrac{\lambda}{2}\|\beta\|^2$, an $L_2$-penalized logistic regression with soft labels;
- M-step for $\theta$: set the conditional probabilities $P(E = t \mid \mathrm{FR} = s)$ proportional to $\sum_n \mathbf 1[E_n = t]\,\omega_{sn} + C$.

The RIVER score of an instance is the posterior $P(\mathrm{FR}_n = 1 \mid G_n, E_n, \hat\beta, \hat\theta)$.

## Expansion

Without expression data the best available score is the annotation-only posterior $P(\mathrm{FR} = 1 \mid G, \hat\beta)$; observing an outlier multiplies its odds by the likelihood ratio $\hat\theta_1/\hat\theta_0$ for $E = 1$ (and by $(1-\hat\theta_1)/(1-\hat\theta_0)$ for $E = 0$). Pairs of individuals carrying the same rare variants provide an independent check: the second carrier's outlier status, unused in fitting, labels the first carrier's prediction. On this held-out set RIVER outperformed an annotation-only penalized logistic regression, and ClinVar pathogenic variants had higher RIVER scores than background variants.

## Sources

- X. Li, Y. Kim, E. K. Tsang et al., "The impact of rare variation on gene expression across tissues", Nature (2017), Methods (outlier calling and "RIVER"), <https://doi.org/10.1038/nature24267>.
