# Oracle selection of risk factors and effect groups in MVMR

In the summary-data MVMR model of the [debiased ridge MVMR estimator](debiased-ridge-mvmr-estimator-under-many-weak-instruments.md), suppose the true direct effects $\boldsymbol\beta^* \in \mathbb R^K$ have $K_1$ nonzero entries partitioned into **signal groups** $G_1,\dots,G_L$: within a group all effects have the same magnitude, with signs $s_k$. Let $C_g$ be the $L\times K$ matrix with $C_{g,lk} = \bar s_l s_k/|G_l|$ for $k \in G_l$ (and $0$ otherwise), where $\bar s_l$ is the sign of the smallest index in $G_l$, so that $C_g\boldsymbol\beta^*$ are the group effects.

**MVMR-PACS estimator.** Given a consistent, asymptotically normal initial estimator $\tilde{\boldsymbol\beta}$ (e.g. debiased ridge), sample correlations $\hat r_{km}$ between exposures, an exponent $\tau > 0$ and a tuning parameter $\lambda$, minimize

$$\tfrac12\boldsymbol\beta^\top(\hat\Pi^\top W\hat\Pi - V)_+\boldsymbol\beta - \hat{\boldsymbol\Gamma}^\top W\hat\Pi\boldsymbol\beta + \lambda\Big\{\sum_k w_k|\beta_k| + \sum_{k<m} w_{km(-)}|\beta_k - \beta_m| + \sum_{k<m} w_{km(+)}|\beta_k + \beta_m|\Big\}$$

with adaptive weights $w_k = |\tilde\beta_k|^{-\tau}$, $w_{km(\mp)} = (1 \mp \hat r_{km})^{-\tau}|\tilde\beta_k \mp \tilde\beta_m|^{-\tau}$. The fused terms shrink effects of highly correlated exposures toward equality (or opposite equality), so groups need not be specified in advance.

Encode the target pattern by $\boldsymbol\theta^* = (\boldsymbol\beta^*, (\beta^*_k - \beta^*_m)_{k<m}, (\beta^*_k + \beta^*_m)_{k<m})$ and let $\mathcal B$ be its support (which exposures are null and which pairs share effects), $\mathcal B_n$ the corresponding support of the estimate.

**Theorem (oracle properties).** Assume the standard MVMR conditions, $\mu_{n,\min}/\sqrt p \to \infty$, no dominant SNP ($\max_j\gamma_{jk}^2\sigma_{Xjk}^{-2}/(\mu_{n,\min}+p) \to 0$), and, with $r_n = \mu_{n,\min}/\sqrt{\mu_{n,\min}+p}$,

$$\lambda_n/r_n \to 0, \qquad \lambda_n r_n^{\tau-1} \to \infty, \qquad \lambda_n r_n^{\tau+1}/\mu_{n,\max} \to \infty.$$

Then

1. (selection and grouping consistency) $\mathbb P(\mathcal B_n = \mathcal B) \to 1$;
2. (asymptotic normality of group effects) $\mathbb V_g^{-1/2}(\Pi_g^\top W\Pi_g)\big(C_g\hat{\boldsymbol\beta}_{\rm PACS} - C_g\boldsymbol\beta^*\big) \xrightarrow{d} N(\mathbf 0, I_L)$, where $\Pi_g = \Pi G^\top$ collapses SNP–exposure associations onto the $L$ groups and $\mathbb V_g$ is the sandwich variance of the grouped score.

With grouping disabled ($w_{km(\pm)} = 0$) this reduces to the adaptive-lasso MVMR estimator, with the same oracle properties for the set of causal exposures. In the many-weak-instrument regime $\mu_{n,\min} = \Theta(p)$ one has $r_n = \Theta(\sqrt p)$ and the conditions only require $\lambda_n = o(\sqrt p)$ plus growth of $\lambda_n r_n^{\tau\pm1}$.

## Depends on

- [Debiased ridge MVMR estimator under many weak instruments](debiased-ridge-mvmr-estimator-under-many-weak-instruments.md)

## Expansion

Rescale $\boldsymbol\beta = \boldsymbol\beta^* + \mathbf u/r_n$. The debiased quadratic loss converges, after rescaling, to a Gaussian quadratic form in $\mathbf u$, while each penalty term behaves like $\lambda_n r_n^{-1} w\, r_n(|\theta^* + u/r_n| - |\theta^*|)$: for $\theta^* \ne 0$ the weight tends to $|\theta^*|^{-\tau}$ and the term vanishes since $\lambda_n/r_n \to 0$, while for $\theta^* = 0$ the weight is of order $r_n^\tau$ and the term diverges unless $u = 0$, because $\lambda_n r_n^{\tau-1} \to \infty$. Epi-convergence gives selection consistency and asymptotic normality on the reduced (grouped) design, as for the adaptive lasso.

## Sources

- Yinxiang Wu, Neil M. Davies, Ting Ye, "Group Identification and Variable Selection in Multivariable Mendelian Randomization with Highly Correlated Exposures", arXiv (2025). MVMR-PACS definition, Section on theoretical analysis, Theorem 1, Theorems 3–4. <https://doi.org/10.48550/arXiv.2511.12375>
