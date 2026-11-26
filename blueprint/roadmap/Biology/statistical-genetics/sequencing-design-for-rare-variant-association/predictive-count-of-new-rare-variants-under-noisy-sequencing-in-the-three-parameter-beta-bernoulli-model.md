# Predictive count of new rare variants under noisy sequencing in the three-parameter beta–Bernoulli model

**Model.** Genetic variants (relative to a reference genome) carried by individual $n$ form a Bernoulli process $X_n \mid \Theta \sim \mathrm{BeP}(\Theta)$: variant $\ell$ is present independently with probability $\theta_\ell$, where $\Theta = \sum_{\ell\ge1}\theta_\ell\delta_{\omega_\ell}$ is a three-parameter beta process $\mathrm{3BP}(\alpha, c, \sigma)$, the Poisson point process with Lévy intensity
$$\alpha\,\frac{\Gamma(1+c)}{\Gamma(1-\sigma)\Gamma(c+\sigma)}\,\theta^{-1-\sigma}(1-\theta)^{c+\sigma-1}\,\mathbf{1}_{[0,1]}(\theta)\,d\theta,$$
$\alpha > 0$, $\sigma \in [0,1)$, $c > -\sigma$ ($\sigma > 0$ gives power-law growth of the number of distinct variants). Sequencing at depth $\lambda$ reads each locus $C \sim \mathrm{Pois}(\lambda)$ times, each read is correct with probability $1 - p_{\mathrm{err}}$, and a variant is called if at least $D$ correct reads support it. Then the observed genotype is $Z_n \mid \Theta \sim \mathrm{BeP}(\phi\Theta)$ with detection probability
$$\phi(\lambda, D, p_{\mathrm{err}}) = \sum_{d \ge D} e^{-\lambda(1-p_{\mathrm{err}})}\frac{\big(\lambda(1-p_{\mathrm{err}})\big)^d}{d!}.$$

**Proposition.** Let $Z_1, \dots, Z_N$ be pilot samples sequenced at depth $\lambda_{\mathrm{pilot}}$, and plan $M$ follow-up samples at depth $\lambda_{\mathrm{follow}}$; write $\phi_{\mathrm{pilot}}, \phi_{\mathrm{follow}}$ for the detection probabilities. For $k \in \{1, \dots, M\}$, the number $U_N^{(M,k)}$ of variants not seen in the pilot that appear exactly $k$ times among the $M$ follow-up samples satisfies, conditionally on $Z_{1:N}$,
$$U_N^{(M,k)} \sim \mathrm{Pois}(\gamma_k), \qquad \gamma_k = \alpha\binom{M}{k}\phi_{\mathrm{follow}}^k\,\frac{(1+c)_{k-1\uparrow}}{(1-\sigma)_{k-1\uparrow}}\,\mathbb{E}\Big[(1 - \phi_{\mathrm{follow}}B)^{M-k}(1 - \phi_{\mathrm{pilot}}B)^N\Big],$$
with $B \sim \mathrm{Beta}(k - \sigma, c + \sigma)$ and $(a)_{b\uparrow} = \Gamma(a+b)/\Gamma(a)$. By exchangeability, the number of such variants per follow-up sample is $\mathrm{Pois}(\gamma_k/M)$.

## Expansion

Thinning a Poisson number of reads by the error probability gives a Poisson number of correct reads with mean $\lambda(1-p_{\mathrm{err}})$, so detection is an independent coin with probability $\phi$ and the observed process is again a Bernoulli process with rates $\phi\theta_\ell$. By the Poisson-process structure of the beta process, variants unseen in the pilot form a Poisson process with intensity reweighted by $(1 - \phi_{\mathrm{pilot}}\theta)^N$, and the count of those seen exactly $k$ times in $M$ new draws integrates $\binom{M}{k}(\phi_{\mathrm{follow}}\theta)^k(1 - \phi_{\mathrm{follow}}\theta)^{M-k}$ against that intensity, which yields the Beta expectation. Since the power of a burden test grows with the number of rare variants discovered, $\gamma_k$ lets one choose, under a fixed budget, between sequencing more individuals at low depth or fewer at high depth, using pilot data to fit $(\alpha, c, \sigma)$.

## Sources

- L. Masoero, J. Schraiber and T. Broderick, "Bayesian nonparametric strategies for power maximization in rare variants association studies", arXiv:2112.02032 (2021), the Bayesian nonparametric framework section (observational model, sequencing-error model and the remark deriving $\phi$, and the proposition on the distribution of rare variants in the presence of sequencing errors), <https://doi.org/10.48550/arXiv.2112.02032>.
