# Asymptotic independence of ridge screening and biomarker–treatment interaction tests

**Setting.** In a randomized trial with $n$ subjects, subject $i$ has outcome $Y_i$, treatment indicator $T_i$ and $m$ biomarkers (for example gene expression or genotypes) $X_{i1},\dots,X_{im}$. Write $\boldsymbol X_i = (T_i, X_{i1},\dots,X_{im})^\top$.

- **Stage 1 (multivariate screening).** Fit the joint main-effects model

$$E(Y_i \mid \boldsymbol X_i) = \boldsymbol X_i^\top \boldsymbol\delta, \qquad \boldsymbol\delta = (\delta_T, \delta_{X_1},\dots,\delta_{X_m})^\top,$$

by ridge regression, minimizing $L_n(\boldsymbol\delta) + \lambda_n \|\boldsymbol\delta\|_2^2$ (the treatment main effect is included in the model and in the penalty). Rank biomarkers by $|\widehat\delta^{\lambda}_{X_j}|$.
- **Stage 2 (one-at-a-time interaction tests).** For each $j$ fit

$$E(Y_i \mid \boldsymbol V_{ij}) = \boldsymbol V_{ij}^\top \boldsymbol\beta_j, \qquad \boldsymbol V_{ij} = (X_{ij}, T_i, X_{ij}T_i)^\top,\quad \boldsymbol\beta_j = (\beta_{X_j}, \beta_{T_j}, \beta_{X_j\times T})^\top,$$

and test $H_0^j: \beta_{X_j\times T} = 0$, with significance levels allotted by the stage 1 ranking (e.g. the $B$ top-ranked markers at level $(\bar\alpha/2)/B$, the next $2B$ at $(\bar\alpha/4)/(2B)$, and so on, which sum to at most $\bar\alpha$).

Homoscedasticity is assumed: $\operatorname{var}(Y_i\mid\boldsymbol X_i)$ and $\operatorname{var}(Y_i\mid\boldsymbol V_{ij})$ are constant.

**Theorem (between-stage independence).** Fix $j \in \{1,\dots,m\}$. Suppose $X_{ij}$ is independent of $T_i$ (true under randomization), and $E(T_i) = 0$ or $E(X_{ij}) = 0$. Under $H_0^j$,

$$\operatorname{cov}\Big\{ n^{1/2}\big(\widehat\delta^{0}_{X_j} - \delta_{X_j}\big),\ n^{1/2}\big(\widehat\beta_{X_j\times T} - \beta_{X_j\times T}\big) \Big\} \to 0$$

in probability, where $\widehat\delta^{0}$ is the unpenalized ($\lambda_n = 0$) maximum likelihood estimator of the stage 1 model and $\widehat\beta_{X_j\times T}$ the maximum likelihood estimator of the stage 2 model.

**Lemma (ridge asymptotics).** Under standard regularity conditions, if $\lambda_n/n^{1/2} \to \lambda_0 \ge 0$, then

$$n^{1/2}\big(\widehat{\boldsymbol\delta}^{\lambda} - \boldsymbol\delta\big) \xrightarrow{d} \mathcal N\big(-2\lambda_0 \Sigma^{-1}\boldsymbol\delta,\ \sigma^2 \Sigma^{-1}\big)$$

for a constant $\sigma > 0$ and an invertible constant matrix $\Sigma$.

**Corollary.** Under the hypotheses of the theorem and $\lambda_n = O(n^{1/2})$, the same asymptotic zero-covariance holds with $\widehat\delta^{0}_{X_j}$ replaced by the ridge estimator $\widehat\delta^{\lambda}_{X_j}$. Since both estimators are jointly asymptotically normal, the stage 1 ranking statistic and the stage 2 interaction statistic are asymptotically independent under $H_0^j$, so the weighted (or Bonferroni-within-selected-set) stage 2 procedure keeps the family-wise error rate at most $\bar\alpha$ asymptotically.

## Expansion

The stage 1 coefficient of $X_j$ is asymptotically a linear functional of the score $\sum_i \boldsymbol X_i (Y_i - \boldsymbol X_i^\top\boldsymbol\delta)$, and the stage 2 interaction coefficient is a linear functional of $\sum_i \boldsymbol V_{ij}(Y_i - \boldsymbol V_{ij}^\top\boldsymbol\beta_j)$. Their asymptotic covariance is proportional to cross moments such as $E(X_{ij}\cdot X_{ij}T_i)$ and $E(T_i \cdot X_{ij}T_i)$ after partialling out the other regressors; independence of $T_i$ and $X_{ij}$ together with centering of one of them makes the relevant cross moments vanish, and including $T_i$ as a stage 1 regressor removes the remaining treatment–interaction correlation. The ridge penalty only adds a deterministic bias $-2\lambda_0\Sigma^{-1}\boldsymbol\delta$ to the limit (Knight–Fu-type asymptotics), which does not change covariances, giving the corollary. The point of the multivariate stage 1 is that the ranking accounts for correlations among biomarkers, unlike one-marker-at-a-time marginal screening (the earlier two-stage gene–environment interaction schemes), while preserving the independence that the family-wise error guarantee needs.

## Sources

- Jixiong Wang, Ashish Patel, James M. S. Wason and Paul J. Newcombe, "Two-stage penalized regression screening to detect biomarker–treatment interactions in randomized clinical trials", *Biometrics* 78 (2022), 141–150, <https://doi.org/10.1111/biom.13424>. Numbering as in the preprint arXiv:2004.12028v2, <https://arxiv.org/abs/2004.12028v2>: Section 2.2 (weighting scheme), Section 2.3 (ridge stage 1 model) and Section 2.4 (Theorem 1, Lemma 1, Corollary 1).
