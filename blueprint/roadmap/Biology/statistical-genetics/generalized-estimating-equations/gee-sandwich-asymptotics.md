# Asymptotic normality and robust variance of the GEE estimator

In the setting of the [GEE estimator](gee-estimator.md), assume the marginal mean model $\mathbb{E}[Y_i] = \mu_i(\beta)$ is correct, the clusters are independent with bounded sizes, the usual regularity conditions hold, and the nuisance estimates satisfy: given $\beta$ and $\phi$, $\hat\alpha$ is $K^{1/2}$-consistent; given $\beta$, $\hat\phi$ is $K^{1/2}$-consistent; and $|\partial \hat\alpha(\beta, \phi) / \partial \phi| = O_p(1)$. The working correlation $R_i(\alpha)$ need **not** equal the true correlation of $Y_i$.

Then, as $K \to \infty$, $\hat\beta$ is consistent and

$$K^{1/2}(\hat\beta - \beta) \xrightarrow{d} \mathcal{N}(0, V_G),$$

$$V_G = \lim_{K \to \infty} K \Bigl(\sum_{i=1}^K D_i^\top V_i^{-1} D_i\Bigr)^{-1} \Bigl(\sum_{i=1}^K D_i^\top V_i^{-1} \operatorname{Cov}(Y_i)\, V_i^{-1} D_i\Bigr) \Bigl(\sum_{i=1}^K D_i^\top V_i^{-1} D_i\Bigr)^{-1}.$$

$V_G$ is estimated consistently by the "sandwich" estimator obtained by evaluating $D_i, V_i$ at $\hat\beta, \hat\alpha, \hat\phi$ and replacing $\operatorname{Cov}(Y_i)$ by $(Y_i - \hat\mu_i)(Y_i - \hat\mu_i)^\top$. If the working covariance is correct, $V_i = \operatorname{Cov}(Y_i)$, the middle factor cancels one outer factor and $V_G$ reduces to the model-based variance $\lim K \bigl(\sum_i D_i^\top V_i^{-1} D_i\bigr)^{-1}$.

## Expansion

Expand $U(\hat\beta) = 0$ around the true $\beta$: $0 = U(\beta) - \bigl(\sum_i D_i^\top V_i^{-1} D_i\bigr)(\hat\beta - \beta) + o_p(K^{1/2})$. The nuisance conditions make the effect of plugging in $\hat\alpha, \hat\phi$ asymptotically negligible, because $\partial U / \partial \alpha$ has mean zero (it multiplies the mean-zero residual $Y_i - \mu_i$). $K^{-1/2} U(\beta)$ is a normalized sum of independent mean-zero terms with covariance $K^{-1} \sum_i D_i^\top V_i^{-1} \operatorname{Cov}(Y_i) V_i^{-1} D_i$, so the multivariate central limit theorem and Slutsky's lemma give the sandwich limit. Consistency of the empirical middle factor follows from the law of large numbers applied to independent clusters. Efficiency is lost when $R_i$ is misspecified, but validity of inference on $\beta$ is not.

## Sources

- K.-Y. Liang and S. L. Zeger, "Longitudinal data analysis using generalized linear models", Biometrika 73 (1986), 13–22, <https://doi.org/10.1093/biomet/73.1.13>.
