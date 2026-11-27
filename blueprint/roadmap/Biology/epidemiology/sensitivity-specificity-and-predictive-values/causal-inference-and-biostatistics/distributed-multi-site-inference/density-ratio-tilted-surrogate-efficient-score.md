# Density-ratio-tilted surrogate efficient score for multi-site data with site-specific nuisance parameters

Data come from $K$ sites with $n$ observations each: $Y_{ij} \sim f(y;\theta_j)$, $i = 1,\dots,n$, $j = 1,\dots,K$, where $\theta_j = (\beta, \gamma_j) \in \mathbb{R}^d$, $\beta \in \mathbb{R}^p$ is shared by all sites and $\gamma_j \in \mathbb{R}^{d-p}$ is site specific. With $L_j(\theta_j) = n^{-1}\sum_i\log f(y_{ij};\theta_j)$, the pooled log-likelihood is $L_N(\beta,\Gamma) = K^{-1}\sum_j L_j(\beta,\gamma_j)$, $\Gamma = (\gamma_1,\dots,\gamma_K)$, but individual data cannot leave their site.

**Efficient score.** With $I^{(j)} = E\{-\nabla^2 L_j(\theta_j^*)\}$, the site-$j$ efficient score for $\beta$ is

$$s_j(y;\beta,\gamma_j) = \nabla_\beta\log f(y;\beta,\gamma_j) - I^{(j)}_{\beta\gamma}\{I^{(j)}_{\gamma\gamma}\}^{-1}\nabla_\gamma\log f(y;\beta,\gamma_j),$$

which satisfies $E\{\nabla_\gamma s_j\} = 0$; the target is the combined efficient score $S(\beta,\Gamma) = (Kn)^{-1}\sum_{j,i}s_j(y_{ij};\beta,\gamma_j)$.

**Density ratio tilting (eq. 2.1).** The site-1 function

$$g^*(y;\beta) = \frac1K\sum_{j=1}^K\frac{f(y;\beta^*,\gamma_j^*)}{f(y;\beta^*,\gamma_1^*)}\,s_j(y;\beta,\gamma_j^*)$$

satisfies $E_{\theta_1^*}\{\nabla^k_\beta g^*(Y_{i1};\beta)\} = E\{\nabla^k_\beta S(\beta,\Gamma^*)\}$ for every $k \ge 0$: site-1 data reproduce all derivatives of the pooled efficient score in expectation.

**Surrogate efficient score estimator (eq. 2.2).** Plug in local estimators $\bar\gamma_j$ and an initial $\bar\beta$ (average of local MLEs $\bar\beta_j$), and replace $I^{(j)}$ by the tilted site-1 estimate $\tilde H^{(1,j)} = -n^{-1}\sum_i\nabla^2\log f(y_{i1};\bar\beta,\bar\gamma_j)\,f(y_{i1};\bar\beta,\bar\gamma_j)/f(y_{i1};\bar\beta,\bar\gamma_1)$, giving $g(y;\beta,\bar\beta,\bar\Gamma)$ and $U_1(\beta) = n^{-1}\sum_i g(y_{i1};\beta,\bar\beta,\bar\Gamma)$. Each site $j$ transmits only the $p$-vector

$$S_j(\bar\beta,\bar\gamma_j) = \nabla_\beta L_j(\bar\beta,\bar\gamma_j) - \bar H^{(j)}_{\beta\gamma}(\bar H^{(j)}_{\gamma\gamma})^{-1}\nabla_\gamma L_j(\bar\beta,\bar\gamma_j)$$

(with $\bar H^{(j)}$ the local Hessian blocks) and its local estimates. Site 1 solves

$$\tilde U(\beta;\bar\beta,\bar\Gamma) = U_1(\beta;\bar\beta,\bar\Gamma) + \frac1K\sum_{j=1}^K S_j(\bar\beta,\bar\gamma_j) - U_1(\bar\beta;\bar\beta,\bar\Gamma) = 0$$

for $\tilde\beta$. Algorithm 1 iterates: broadcast $\bar\beta^{(t)} = \tilde\beta^{(t-1)}$, refit $\bar\gamma_j^{(t)} = \arg\max_\gamma L_j(\bar\beta^{(t)},\gamma)$, retransmit $S_j$, re-solve. Each round costs $O(Kd)$ numbers of communication.

## Expansion

$\tilde U$ is a first-order-corrected surrogate: at $\beta = \bar\beta$ it equals the exact pooled efficient score built from transmitted gradients, while its dependence on $\beta$ (all higher derivatives) is taken from site-1 data reweighted by the density ratio, so that site 1 mimics the mixture of all sites. Using the efficient score rather than the full score projects out the $\gamma_j$ directions, so errors in the many site-specific nuisance estimates enter only at second order. A one-step variant (Remark 2) is $\tilde\beta^O = \bar\beta - \{\nabla_\beta U_1(\bar\beta)\}^{-1}S(\bar\beta,\bar\Gamma)$. The convergence and efficiency guarantees are in [the companion article](surrogate-efficient-score-convergence-and-efficiency.md).

## Sources

- R. Duan, Y. Ning and Y. Chen, *Heterogeneity-aware and communication-efficient distributed statistical inference*, Biometrika (2022). <https://doi.org/10.1093/biomet/asab007>
