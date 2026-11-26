# Convergence and efficiency of the surrogate efficient score estimator

Use the model and the [density-ratio-tilted surrogate efficient score estimator](density-ratio-tilted-surrogate-efficient-score.md) $\tilde\beta^{(T)}$ after $T$ iterations of Algorithm 1, with $K$ sites of $n$ observations, $N = Kn$. Assume (Assumptions 1-5 of the source): the parameter space of $\beta$ is compact and convex with $\beta^*$ interior; local strong convexity $\mu_-I_d \preceq I^{(j)}(\theta_j^*) \preceq \mu_+I_d$ for all $j$; sub-exponential first and second log-likelihood derivatives; $(\beta^*,\gamma_j^*)$ uniquely maximizes $E\log f(Y_{ij};\beta,\gamma_j)$; and Lipschitz Hessians (including the density-ratio-tilted Hessian) with sub-exponential Lipschitz envelopes.

**Lemma 1 (pooled MLE).** The global maximum likelihood estimator $\hat\beta$ satisfies $E\|\hat\beta - \beta^*\|_2 \le C_1/(Kn)^{1/2} + C_2/n$. It is $O_P(N^{-1/2})$ when $K/n = O(1)$. For fixed $n$ as $K \to \infty$ this upper bound does not vanish; that alone proves no lower bound, but bias *can* persist, as in the Neyman–Scott problem, where the site nuisances enter the common parameter's likelihood equations. It need not persist: if the common parameter and the site nuisances govern independent coordinates of $Y_{ij}$ (for example a common Bernoulli parameter in one coordinate), the pooled MLE of the common parameter is consistent as $K \to \infty$ with $n$ fixed.

**Theorem 1 (one round).** If $n \gtrsim \log K$, then $E\|\tilde\beta^{(1)} - \hat\beta\|_2 \le C/n$.

**Theorem 2 (two or more rounds).** If $n \gtrsim \log K$, then for $T \ge 2$, $E\|\tilde\beta^{(T)} - \hat\beta\|_2 \le C_1/(K^{1/2}n) + C_2/n^{3/2}$. When $K/n \to 0$ this is smaller by a factor $n^{-1/2}$ than the distance from $\hat\beta$ of the simple average of local estimators, independently of the nuisance dimension.

**Theorem 3 (asymptotic efficiency).** Let $I^{(j)}_{\beta|\gamma} = I^{(j)}_{\beta\beta} - I^{(j)}_{\beta\gamma}(I^{(j)}_{\gamma\gamma})^{-1}I^{(j)}_{\gamma\beta}$ be the partial information of site $j$ and $I_{\beta|\gamma} = K^{-1}\sum_j I^{(j)}_{\beta|\gamma}$. If $K = Cn^r$ with fixed $r \in [0,1)$, then for every $T \ge 1$, as $n \to \infty$,

$$Kn\,(\tilde\beta^{(T)} - \beta^*)^{\top}I_{\beta|\gamma}(\tilde\beta^{(T)} - \beta^*) \to \chi^2_p,$$

so $\tilde\beta^{(T)}$ attains the Cramer-Rao bound $I_{\beta|\gamma}^{-1}/(Kn)$.

**Proposition 1 (averaging is inefficient).** For the average $\bar\beta = K^{-1}\sum_j\bar\beta_j$ of local MLEs, under the conditions of Theorem 3,

$$Kn\,(\bar\beta - \beta^*)^{\top}\Big\{\frac1K\sum_{j=1}^K\big(I^{(j)}_{\beta|\gamma}\big)^{-1}\Big\}^{-1}(\bar\beta - \beta^*) \to \chi^2_p,$$

and $K^{-1}\sum_j(I^{(j)}_{\beta|\gamma})^{-1} \succeq (K^{-1}\sum_j I^{(j)}_{\beta|\gamma})^{-1}$. The difference is nonzero whenever the partial informations $I^{(j)}_{\beta|\gamma}$ are not all equal, but it need not be positive definite: heterogeneity confined to some directions of $\beta$ costs efficiency only in those directions, so the comparison is between partial informations, not a strict loss in every direction.

## Expansion

The surrogate equation differs from the pooled efficient score equation only through second-order terms: the mismatch between the site-1 tilted Hessian and the pooled Hessian (order $n^{-1/2}$) multiplies the initial error $\|\bar\beta - \hat\beta\|$, and nuisance errors enter quadratically thanks to the orthogonality of the efficient score. Iterating replaces the crude initial error by the already-improved $\tilde\beta^{(1)}$, giving Theorem 2. The restriction $r < 1$ cannot be relaxed: at $K \asymp n$ the pooled MLE itself carries an asymptotic bias (Li et al., 2003), which $\tilde\beta^{(T)}$ inherits. The average estimator matches the efficient variance exactly when the partial informations coincide, because the arithmetic mean of inverse informations dominates the inverse of their mean (matrix harmonic-arithmetic mean inequality), with a nonzero gap otherwise. Theorem 4 of the source estimates $I_{\beta|\gamma}$ from site-1 data by density ratio tilting, giving confidence intervals.

## Depends on

- [Density-ratio-tilted surrogate efficient score](density-ratio-tilted-surrogate-efficient-score.md)

## Sources

- R. Duan, Y. Ning and Y. Chen, *Heterogeneity-aware and communication-efficient distributed statistical inference*, Biometrika (2022). <https://doi.org/10.1093/biomet/asab007>
