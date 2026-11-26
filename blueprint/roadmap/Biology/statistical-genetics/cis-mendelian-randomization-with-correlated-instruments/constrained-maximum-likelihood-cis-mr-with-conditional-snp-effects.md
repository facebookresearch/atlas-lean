# Constrained maximum-likelihood cis-MR with conditional SNP effects

**Model.** Let $G_1, \dots, G_m$ be correlated SNPs in one gene region, $X$ an exposure and $Y$ an outcome, with joint (conditional) structural models $X = \sum_i b_{X_i} G_i + \epsilon_X$ and $Y = \theta X + \sum_i r_i G_i + \epsilon_Y$, where $\epsilon_X, \epsilon_Y$ may be correlated (hidden confounding) but are independent of the SNPs. Then the joint SNP-outcome effects satisfy

$$b_{Y} = \theta \, b_{X} + r,$$

and SNP $i$ is a valid instrument when $b_{X_i} \ne 0$ and $r_i = 0$. Marginal GWAS estimates $\hat\beta^*_X$ with standard errors $\sigma^*_X$ (standardized genotypes and phenotype) and an LD matrix $R$ give conditional estimates

$$\hat\beta_X = R^{-1} \hat\beta^*_X, \qquad \Sigma_X = R^{-1} \Omega_X R^{-1}, \qquad \Omega_X = R \circ \sigma^*_X \sigma^{*\top}_X,$$

and likewise $\hat\beta_Y, \Sigma_Y$; the working model is $\hat\beta_X \sim \mathrm{MVN}(b_X, \Sigma_X)$ and $\hat\beta_Y \sim \mathrm{MVN}(\theta b_X + r, \Sigma_Y)$, independent. With log-likelihood

$$\ell(\theta, b_X, r) = -\tfrac12 \Bigl[(\hat\beta_X - b_X)^{\top} \Sigma_X^{-1} (\hat\beta_X - b_X) + (\hat\beta_Y - \theta b_X - r)^{\top} \Sigma_Y^{-1} (\hat\beta_Y - \theta b_X - r)\Bigr],$$

the constrained MLE for $K$ invalid instruments maximizes $\ell$ subject to $\sum_i \mathbf{1}(r_i \ne 0) = K$, and $K$ is chosen by $\mathrm{BIC}(K) = -2 \ell(\hat\theta^{(K)}, \hat b_X^{(K)}, \hat r^{(K)}) + K \log N$ with $N = \min(N_X, N_Y)$.

**Theorem.** Assume (1) the plurality condition: for every index set $A \ne A_0 = \{i : r_i \ne 0\}$ with $|A| = |A_0| = K_0$ there is no $\tilde\theta \ne \theta$ with $b_{Y_i} = \tilde\theta b_{X_i}$ for all $i \notin A$; (2) the normal working model with known $\Sigma_X, \Sigma_Y$; (3) every entry of $\Sigma_X$ and $\Sigma_Y$ lies between $c_1/N$ and $c_2/N$ for positive constants $c_1, c_2$. If the candidate set of $K$ contains $K_0$, then as $N \to \infty$, $\Pr(\hat K = K_0) \to 1$, $\Pr(\hat A_{\hat K} = A_0) \to 1$, the estimator $\hat\theta$ is consistent, and $\sqrt{V}(\hat\theta - \theta_0) \to N(0, 1)$ in distribution, where $V$ is the expected Fisher information of the profile likelihood over the valid instruments.

**Why conditional effects.** In marginal terms $b^*_Y = \theta b^*_X + R r$, so a single pleiotropic SNP ($r = (r_1, 0, \dots, 0)$) makes every SNP correlated with it look pleiotropic, and the plurality condition can hold for $(b_X, b_Y)$ but fail for $(b^*_X, b^*_Y)$. For the same reason all SNPs associated with either trait must be included before conditioning; omitting an outcome-only SNP opens paths from its LD partners to $Y$ that bypass $X$.

## Expansion

At a fixed invalid set the problem is a Gaussian profile likelihood in $(\theta, b_X)$ over the remaining SNPs, so the invalid instruments do not contribute to $\hat\theta$; the theorem is then the usual selection consistency of BIC with a $\log N$ penalty against the $O(1/N)$ sampling variance, combined with identifiability from plurality. The best-subset search is solved heuristically by iteratively ranking SNPs on standardized residuals $(\hat\beta_Y - \tilde\theta \tilde b_X)^2 / \operatorname{diag}(\Sigma_Y)$, and finite-sample selection uncertainty is propagated by resampling $\hat\beta_X, \hat\beta_Y$ from their normal laws.

## Sources

- Z. Lin and W. Pan, "A robust cis-Mendelian randomization method with application to drug target discovery", Nature Communications 15 (2024), 6072, Eqs. (4), (11)–(15), Assumptions 1–3 and Theorem 1. <https://doi.org/10.1038/s41467-024-50385-y> PMCID: PMC11258283.
