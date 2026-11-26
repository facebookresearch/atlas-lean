# One-sided Wald test for higher-order transmission from a single aggregate SIS trajectory

**Setting.** In the simplicial SIS model on $N$ individuals, the number of infecteds $X_t$ is a birth–death chain with birth rate $\lambda_k = \sum_{i=1}^K\beta_i\binom{k}{i}(N-k)$ (pairwise transmission $\beta_1$, triadic transmission $\beta_2$, and so on) and recovery rate $\mu k$. One surviving trajectory is observed continuously on $[0,T]$, with no labels saying which mechanism caused each infection. Inference is carried out under the Doob $h$-transformed $Q$-process (the chain conditioned to avoid extinction), where the conditional MLE $\widetilde{\boldsymbol\theta}_T$ satisfies $\sqrt T(\widetilde{\boldsymbol\theta}_T-\boldsymbol\theta_0)\Rightarrow\mathcal N(0,\mathcal I(\boldsymbol\theta_0)^{-1})$.

**Test.** To test $H_{0}:\beta_i = 0$ against $H_{1}:\beta_i>0$ (e.g. $i=2$: is there triadic transmission?), enlarge the parameter set locally so that $\beta_i$ may take either sign while all tilted intensities stay positive and the killed generator stays irreducible, and let $\widehat{\mathcal I}_T$ be a consistent estimator of the Fisher information. Then

$$
Z_{i,T} = \frac{\widetilde\beta_{i,T}}{\sqrt{(\widehat{\mathcal I}_T^{-1})_{ii}/T}} \Rightarrow \mathcal N(0,1)\quad\text{under } H_0 ,
$$

so the test rejecting when $Z_{i,T}>z_{1-\alpha}$ has asymptotic level $\alpha$, with one-sided $p$-value $1-\Phi(Z_{i,T})$. Equivalently, the projected Wald statistic $W_{i,T} = (\max\{0,Z_{i,T}\})^2$ has the boundary-mixture null limit $\tfrac12\chi^2_0 + \tfrac12\chi^2_1$.

## Expansion

Because the null value $\beta_i = 0$ is on the boundary of the epidemiological parameter space $(0,\infty)^{K+1}$, the unconstrained estimator is used on a local open enlargement, where the asymptotic normality of the conditional MLE (Theorem 6.5) still holds under the same regularity and non-degeneracy conditions; studentizing the $i$-th coordinate gives the standard normal limit. Squaring the positive part of a standard normal gives the $\tfrac12\chi^2_0+\tfrac12\chi^2_1$ mixture familiar from boundary testing. Simulations with $N=100$ and $T=1000$ match the $\mathcal N(0,1)$ null law.

## Depends on

- [Survival-conditioned likelihood inference for composite birth–death processes](survival-conditioned-likelihood-for-composite-birth-death-processes.md)

## Sources

- M. Lalovic, N. Georgiou, I. Z. Kiss, "Likelihood-based inference for birth-death processes with composite birth mechanisms", arXiv:2604.20422 (2026), Section 6.1 (one-sided Wald test and the triadic-transmission example), <https://doi.org/10.48550/arXiv.2604.20422>.
