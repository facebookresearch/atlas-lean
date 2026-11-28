# Full-DFE model of polymorphism and divergence counts

Let $n$ be the sample size of the ingroup. Sites are neutral (*neut*) or selected (*sel*); a new mutation at a selected site has scaled selection coefficient $S = 4 N_e s$ drawn from a distribution of fitness effects (DFE) $\varphi$ on $\mathbb{R}$, covering both deleterious ($S < 0$) and beneficial ($S > 0$) mutations. For $0 < x < 1$ put

$$B(i, n, x) = \binom{n}{i} x^i (1 - x)^{n-i}, \qquad H(S, x) = \frac{1 - e^{-S(1-x)}}{x (1 - x)(1 - e^{-S})}, \qquad H(0, x) = \frac{1}{x}.$$

**Unfolded site-frequency spectrum.** With population mutation rate $\theta$, the expected number $P_z(i)$ of sites with $i$ derived alleles ($1 \le i < n$) is

$$\mathbb{E}[P_{\mathrm{neut}}(i)] = \frac{\theta}{i}, \qquad \mathbb{E}[P_{\mathrm{sel}}(i) \mid S] = \theta \int_0^1 B(i, n, x)\, H(S, x)\, dx,$$

and $\mathbb{E}[P_{\mathrm{sel}}(i) \mid \varphi] = \int \mathbb{E}[P_{\mathrm{sel}}(i) \mid S]\, \varphi(S)\, dS$. Departures from equilibrium that affect neutral and selected sites alike (demography, sampling, linkage) are absorbed by nuisance factors $r_i > 0$, $\mathbb{E}[P_z(i) \mid \theta, r_i, \varphi] = r_i\, \mathbb{E}[P_z(i) \mid \theta, \varphi]$, and misidentified ancestral states (probability $\epsilon$) by the mixture

$$(1 - \epsilon)\, \mathbb{E}[P_z(i) \mid \theta, r_i, \varphi] + \epsilon\, \mathbb{E}[P_z(n - i) \mid \theta, r_i, \varphi] = r_i \big[(1 - \epsilon)\, \mathbb{E}[P_z(i) \mid \theta, \varphi] + \epsilon\, \mathbb{E}[P_z(n - i) \mid \theta, \varphi]\big],$$

with the same factor $r_i$ in both terms.

**Divergence counts.** With composite divergence parameter $\lambda = T\theta$,

$$\mathbb{E}[D_{\mathrm{neut}} \mid \lambda] = \lambda, \qquad \mathbb{E}[D_{\mathrm{sel}} \mid \lambda, S] = \lambda \frac{S}{1 - e^{-S}},$$

to which the expected count of ingroup polymorphisms misattributed as fixed, $\theta r_n / n$ and $\theta r_n \int_0^1 B(n, n, x) H(S, x)\, dx$ respectively, is added. The DFE used is a mixture: with probability $1 - p_b$ a reflected gamma with mean $S_d < 0$ and shape $b$, and with probability $p_b$ an exponential with mean $S_b > 0$. Mutation-rate variation across fragments is a gamma law on $\theta$, which turns the Poisson counts into negative binomial counts.

## Remarks

$\tfrac12 H(S, x)\,dx$ is the expected time a new semidominant mutation with scaled coefficient $S$ spends at frequency in $[x, x + dx]$ (Wright's sojourn density), so integrating it against binomial sampling gives the Poisson-random-field spectrum; $S/(1 - e^{-S}) = \lim_{x \to 1} H(S, x)$ is the fixation rate of a selected mutation relative to a neutral one. Because the nuisance factors $r_i$ multiply neutral and selected classes equally, only the *shape difference* between the selected and neutral spectra informs $\varphi$, which makes the inference robust to demography when selection is weak. Beneficial mutations sit at high derived frequencies in the unfolded spectrum, so they leave a signal in polymorphism data; ignoring them (fitting only a deleterious DFE) biases both the deleterious DFE and the estimated adaptive proportion. For very large $S_b$, $H(S, x) \to 1/(x(1-x))$ and polymorphism counts lose the information to separate $p_b$ from $S_b$, although the adaptive proportion, which depends mainly on their product, stays well estimated.

## Depends on

- [Site-frequency spectrum under a distribution of fitness effects](dfe-sfs.md)
- [Gamma distribution of fitness effects](gamma-dfe.md)

## Sources

- P. Tataru, M. Mollion, S. Glémin et al., "Inference of distribution of fitness effects and proportion of adaptive substitutions from polymorphism data", Genetics 207 (2017), <https://doi.org/10.1534/genetics.117.300323>, PMCID PMC5676230. Equations 1–7 and the section on the DFE parameterization.
