# Zero-inflated Poisson factor model for microbiome read counts

Let $A \in \mathbb N_0^{n \times m}$ hold read counts of $m$ taxa in $n$ samples, and let

$$N_i = \frac{\sum_{j} A_{ij}}{\operatorname{median}_{i'} \sum_j A_{i'j}}$$

be the relative library size of sample $i$. Every sample is assumed to have a positive total count $\sum_j A_{ij} > 0$, so that each $N_i$ is positive and the offsets $\ln N_i$ used below are finite. The **zero-inflated Poisson factor analysis (ZIPFA)** model of rank $K < \min(n, m)$ assumes independent entries with

$$A_{ij} \sim \begin{cases} 0, & \text{with probability } p_{ij},\\ \mathrm{Poisson}(N_i \lambda_{ij}), & \text{with probability } 1 - p_{ij},\end{cases}$$

$$\ln \lambda_{ij} = \sum_{k=1}^{K} u_{ik} v_{jk}, \qquad \operatorname{logit}(p_{ij}) = -\tau \ln \lambda_{ij}, \quad \tau > 0,$$

where $\mathrm{Poisson}(\mu)$ is the [Poisson law](../../Probability/central-limit-theorems/poisson-limit-theorem/poisson-prob-measure.md) of mean $\mu$, so $\Lambda = (\ln\lambda_{ij}) = U V^{\top}$ with scores $U \in \mathbb R^{n \times K}$ and loadings $V \in \mathbb R^{m \times K}$. Equivalently $p_{ij} = 1/(1 + \lambda_{ij}^{\tau})$: the probability of a structural ("true") zero decreases as the normalized Poisson rate increases, with one shape parameter $\tau$ shared by all entries. The probability of observing a zero is

$$\Pr(A_{ij} = 0) = p_{ij} + (1 - p_{ij})\, e^{-N_i \lambda_{ij}},$$

and the likelihood is

$$L(A) = \prod_{i,j} \left\{ p_{ij}\, \mathbf 1[a_{ij} = 0] + (1 - p_{ij})\, \frac{(N_i \lambda_{ij})^{a_{ij}} e^{-N_i \lambda_{ij}}}{a_{ij}!} \right\}.$$

Parameters are fitted by alternating maximization: with $U$ fixed, $(V, \tau)$ solve a zero-inflated Poisson regression with offsets $\ln N_i$, fitted by an EM algorithm, and then the roles of $U$ and $V$ are swapped. Each step does not decrease $L(A)$, which is bounded by $1$, so the likelihood values converge. The rank $K$ is chosen by maximizing a cross-validated likelihood.

## Expansion

The coupling $\operatorname{logit}(p) = -\tau \ln\lambda$ links the two natural parameters of the mixture (the log Poisson mean and the logit of the zero probability) linearly, motivated by fitting a zero-inflated negative binomial law to each taxon in oral microbiome data and observing a logistic decrease of the zero probability in $\ln\lambda$. Unlike factor analysis of log-transformed compositions, the model uses raw counts with library size as an offset, so no pseudocounts or rarefying are needed. With $U$ fixed, the conditional problem for each taxon is a zero-inflated Poisson regression in which the linear predictor is the log of the Poisson-component rate, $\ln \lambda_i = X_i^\top \beta$, with offset $\ln N_i$ and $\operatorname{logit}(p_i) = -\tau \ln \lambda_i$; it is not the log of the observed mean, since $\mathbb E(Y_i / N_i \mid X_i) = (1 - p_i)\lambda_i$ (for $\lambda_i = 1$ the observed mean is $1/2$, while $X_i^\top\beta = 0$). The problem is solved by EM with the latent indicator of a structural zero. In simulations ZIPFA had lower or comparable $L_2$ loss than Poisson SVD with offsets and a zero-inflated quasi-Poisson factor model, and converged in settings where the latter often failed; the fitted scores then serve as low-dimensional covariates for association with clinical outcomes.

## Depends on

- [Poisson law as a probability measure](../../Probability/central-limit-theorems/poisson-limit-theorem/poisson-prob-measure.md)

## Sources

- T. Xu, R. T. Demmer and G. Li, "Zero-inflated Poisson factor model with application to microbiome read counts", Biometrics (2020), Section 2 (Section 2.1 model setup, Equation 1 likelihood, Section 2.2 estimation, Section 2.3 ZIP regression, rank selection), <https://doi.org/10.1111/biom.13272> (PMC7594114).
