# Limiting ABC Bayes factor and the cross-model sufficiency gap

**Setting.** Approximate Bayesian computation (ABC) for model choice works as follows. Draw a model index $m$ from its prior, a parameter $\theta_m\sim\pi_m$, and pseudo-data $z\sim f_m(\cdot\mid\theta_m)$. Accept the draw when $\rho\{\eta(z),\eta(y)\}\le\epsilon$ for a summary statistic $\eta$ and tolerance $\epsilon$. Then estimate the posterior model probabilities by the acceptance frequencies. This is the standard tool for comparing demographic and phylogeographic scenarios in population genetics, for example in DIY-ABC. With equal prior model weights, the ABC estimate of the Bayes factor $B_{12}$ is the ratio of acceptance counts.

**Statement.**

1. *(Limit of ABC.)* As the number of simulations tends to infinity, the ABC estimate converges to

$$B^\epsilon_{12}(y)=\frac{\iint\mathbf 1\{\rho(\eta,\eta(y))\le\epsilon\}\,\pi_1(\theta_1)f_1^\eta(\eta\mid\theta_1)\,d\eta\,d\theta_1}{\iint\mathbf 1\{\rho(\eta,\eta(y))\le\epsilon\}\,\pi_2(\theta_2)f_2^\eta(\eta\mid\theta_2)\,d\eta\,d\theta_2},$$

where $f_i^\eta$ is the density of $\eta(z)$ under model $i$. As $\epsilon\to0$, this tends to

$$B^\eta_{12}(y)=\frac{\int\pi_1(\theta_1)f_1^\eta(\eta(y)\mid\theta_1)\,d\theta_1}{\int\pi_2(\theta_2)f_2^\eta(\eta(y)\mid\theta_2)\,d\theta_2},$$

the Bayes factor based on observing $\eta(y)$ alone.
2. *(Sufficiency gap.)* Suppose $\eta$ is sufficient for each model separately, so that $f_i(y\mid\theta_i)=g_i(y)\,f_i^\eta(\eta(y)\mid\theta_i)$. Then

$$B_{12}(y)=\frac{g_1(y)}{g_2(y)}\,B^\eta_{12}(y).$$

So ideal ABC with infinite computing power recovers the true Bayes factor only when $g_1=g_2$, that is when $\eta$ is sufficient *across* models for $(m,\theta_m)$. Gibbs random fields and encompassing exponential families have this property; complex population-genetic models generally do not.
3. *(The discrepancy can be arbitrary.)* Compare i.i.d. Poisson$(\lambda)$ data with $\lambda\sim\mathrm{Exp}(1)$ against geometric$(p)$ data with $p\sim U(0,1)$. The sum $S=\sum y_i$ is sufficient in each model, and the Bayes factor based on $S$ satisfies, almost surely,

$$\lim_{n\to\infty}B^S_{12}(y)=\theta_0^{-1}(\theta_0+1)^2e^{-\theta_0},$$

where $\theta_0=\mathbb E[y_i]$. This limit is a finite number fixed by $\theta_0$ alone, so the summary-based Bayes factor cannot become decisive however much data accumulates. In the normal case $N(\mu,\sigma_1^2)$ versus $N(\mu,\sigma_2^2)$ with a common $N(0,a^2)$ prior, $\lim_nB^S_{12}=1$ almost surely. So the summary-based Bayes factor carries no information at all.

The approximation error of ABC posterior model probabilities therefore need not shrink with more computation. Without additional empirical checks, such as simulation-based assessment of the discriminative power of the chosen summaries, ABC model choice is not validated.

## Expansion

Item 1 replaces $z$ by $\eta=\eta(z)$ in the acceptance integrals and applies L'Hôpital's rule (a Lebesgue differentiation argument) as $\epsilon\to0$. Item 2 is the factorization theorem inserted into the marginal likelihoods: the factor $g_i(y)$ does not depend on $\theta_i$, so it comes out of the integral. In the Poisson–geometric example, the conditional law of the sample given $S$ is multinomial $\mathcal M(S;1/n,\dots,1/n)$ under the Poisson model. Under the geometric model it is uniform over the compositions of $S$ into $n$ parts. The factor $g_1(y)/g_2(y)$ thus carries information about the model that $S$ discards. The limit in item 3 follows from the large-$n$ asymptotics of the two marginal laws of $S$ evaluated at $S\approx n\theta_0$. Under the first model $S$ is a Poisson–exponential mixture, and under the second a negative-binomial–uniform mixture.

These are the limit computation of Section 2.3, the Gibbs-random-field discussion (Section 3.1), the Poisson–geometric lemma (Section 3.2) and the normal lemma (supplementary results) of the source.

## Sources

- C. P. Robert, J.-M. Cornuet, J.-M. Marin, N. S. Pillai, "Lack of confidence in approximate Bayesian computation model choice", arXiv:1102.4432 (2011). <https://doi.org/10.48550/arXiv.1102.4432>
