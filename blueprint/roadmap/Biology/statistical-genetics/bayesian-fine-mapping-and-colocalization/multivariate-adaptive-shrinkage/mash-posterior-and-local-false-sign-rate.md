# mash posterior, local false sign rate and the exchangeable-Z model

In the [mash model](mash-mixture-prior-and-marginal-likelihood.md) with fitted weights $\hat\pi$ and components $\Sigma_p$, the posterior of each effect vector is again a normal mixture. As in the source, every error covariance $V_j = S_j C S_j$ (and $V$ below) is symmetric positive definite; this is what makes $V^{-1}$, $(U + V)^{-1}$ and the Gaussian densities $N_R(\,\cdot\,; 0, \Sigma_p + V_j)$ in the responsibilities well defined and nondegenerate for every positive semidefinite $U$ and $\Sigma_p$. For a single component, if $b \sim N_R(0, U)$ with $U$ positive definite and $\hat b \mid b \sim N_R(b, V)$ then

$$b \mid \hat b \sim N_R(\tilde\mu, \tilde U), \qquad \tilde U = (U^{-1} + V^{-1})^{-1}, \quad \tilde\mu = \tilde U V^{-1}\hat b. \tag{6, 7}$$

For singular $U$ (for example the rank-one components) the same posterior is $\tilde U = U - U(U + V)^{-1}U$, $\tilde\mu = U(U + V)^{-1}\hat b$.

For the mixture,

$$p(b_j \mid \hat b_j, V_j, \hat\pi) = \sum_{p=1}^{P}\tilde\pi_{jp}\, N_R(b_j; \tilde\mu_{jp}, \tilde U_{jp}), \qquad \tilde\pi_{jp} = \frac{\hat\pi_p N_R(\hat b_j; 0, \Sigma_p + V_j)}{\sum_{p'} \hat\pi_{p'} N_R(\hat b_j; 0, \Sigma_{p'} + V_j)},$$

with $\tilde U_{jp} = \tilde U(\Sigma_p, V_j)$ and $\tilde\mu_{jp} = \tilde\mu(\Sigma_p, V_j, \hat b_j)$. The posterior mean and variance are

$$E(b_j \mid \cdot) = \sum_p \tilde\pi_{jp}\tilde\mu_{jp}, \qquad \mathrm{Var}(b_{jr} \mid \cdot) = \sum_p \tilde\pi_{jp}\bigl(\tilde U_{jp, rr} + \tilde\mu_{jp, r}^2\bigr) - \Bigl(\sum_p \tilde\pi_{jp}\tilde\mu_{jp, r}\Bigr)^2. \tag{8}$$

The **local false sign rate** of effect $j$ in condition $r$ is

$$\mathrm{lfsr}_{jr} = \min\{P(b_{jr} \ge 0 \mid D),\ P(b_{jr} \le 0 \mid D)\},$$

computed from the univariate normal-mixture marginals. It is at least the local false discovery rate $P(b_{jr} = 0 \mid D)$. The **Bayes factor** for $b_j \neq 0$ against the global null is $\mathrm{BF}_j = p(\hat b_j \mid \hat\pi, U, V_j)/N_R(\hat b_j; 0, V_j)$.

**Exchangeable effects versus exchangeable $Z$.** Model (3) assumes $b_j$ independent of $V_j$ (EE). The EZ model instead places the mixture prior on $S_j^{-1}b_j$. It is fitted by running the same procedure on $\hat b_{jr} = z_{jr}$ with $\hat s_{jr} = 1$ and the same $C$, and it yields lfsr values from $Z$-scores alone. Its posterior means estimate $S_j^{-1}b_j$.

## Proof sketch

Equations (6)–(7) are the normal–normal conjugate update: the posterior precision is the sum of prior and data precisions, and the mean is the data precision-weighted estimate. Mixing over components with responsibilities $\tilde\pi_{jp}$ (Bayes' rule using the marginal (4)) gives the mixture posterior, and (8) is the law of total variance. Because $P(b_{jr} \ge 0) + P(b_{jr} \le 0) = 1 + P(b_{jr} = 0)$, the smaller of the two is at least $P(b_{jr} = 0)$. So declaring "confident sign" whenever $\mathrm{lfsr} \le \alpha$ is more conservative than thresholding the lfdr, and it is less sensitive to the shape of the prior near zero. Shrinkage borrows strength across conditions through the learned $U_k$. An effect seen strongly in a few conditions has its estimates in correlated conditions pulled toward the shared pattern rather than toward zero.

## Depends on

- [The mash mixture prior and its marginal likelihood](mash-mixture-prior-and-marginal-likelihood.md)
- [Multivariate Gaussian density function](../../../../Probability/distributions/continuous/multivariate-normal-distribution/gaussian-density/multivariate-gaussian-pdfreal.md)

## Sources

- S. M. Urbut, G. Wang, P. Carbonetto and M. Stephens, "Flexible statistical methods for estimating and testing effects in genomic studies with multiple conditions", Nature Genetics 51 (2019), 187–195 (online 2018), Online Methods ("Posterior calculations", Equations (6)–(8); "Bayes Factors testing global null"; "The EZ model, and applying mash to Z scores"), <https://doi.org/10.1038/s41588-018-0268-8>, PMCID PMC6309609.
