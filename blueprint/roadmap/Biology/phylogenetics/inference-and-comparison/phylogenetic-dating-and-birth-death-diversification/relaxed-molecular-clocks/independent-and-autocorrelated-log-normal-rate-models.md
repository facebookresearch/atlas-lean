# Independent and autocorrelated log-normal rate models

**Setting.** A rooted time tree has node ages $t_v$ and branches $b$ with time durations $\Delta t_b$. A relaxed molecular clock assigns a substitution rate $r_b > 0$ to every branch, so that the expected number of substitutions per site on $b$ is $d_b = r_b \Delta t_b$. Let $\mu > 0$ be the mean rate (for one locus) and $\sigma^2 > 0$ a dispersion parameter.

**Independent rates (IR).** The branch rates are i.i.d. log-normal with mean $\mu$:

$$\log r_b \sim \mathcal{N}\big(\log\mu - \tfrac{1}{2}\sigma^2,\ \sigma^2\big), \qquad \mathbb{E}[r_b] = \mu,\ \ \mathrm{Var}(\log r_b) = \sigma^2 .$$

**Autocorrelated rates (AR, geometric Brownian motion).** The root rate is $\mu$, and the rate at a node $v$ with parent $u$ is drawn given the parent's rate as

$$\log r_v \mid r_u \sim \mathcal{N}\big(\log r_u - \tfrac{1}{2}\sigma^2 \Delta t_{uv},\ \sigma^2 \Delta t_{uv}\big),$$

where $\Delta t_{uv} = t_u - t_v$; branch rates are computed from the rates at the branch ends.

**Proposition.**

1. Under AR, $\mathbb{E}[r_v \mid r_u] = r_u$, and the rates along any root-to-tip path form a mean-preserving geometric Brownian motion: $\mathrm{Var}(\log r_v - \log r_u) = \sigma^2 \Delta t_{uv}$.
2. Under AR, two sister lineages that split at age $t$ have $\mathrm{Var}(\log r_1 - \log r_2 \mid \text{split rate}) = 2\sigma^2 t$, which tends to $0$ as $t \to 0$; under IR the corresponding variance is $2\sigma^2$ at every time scale.
3. Under both models only the products $d_b = r_b \Delta t_b$ enter the sequence likelihood, so rates and times are not separately identifiable without a prior on times (fossil calibrations).

## Expansion

If $\log X \sim \mathcal{N}(m, s^2)$ then $\mathbb{E}[X] = e^{m + s^2/2}$, which gives the mean statements; independence of Gaussian increments over disjoint branches gives the Brownian-motion variance. Item 2 says that AR behaves like a local clock among close relatives while allowing rates to drift apart across distant clades, which the source finds biologically appealing, whereas IR assumes the same rate variance at all time scales. On a 372-species primate data set the source computes marginal likelihoods of the strict clock, IR and AR models by thermodynamic integration with Gaussian quadrature, finds Bayes factors strongly favoring AR, and finds that IR gives considerably older ages for the deepest nodes.

## Sources

- M. dos Reis, G. F. Gunnell, J. Barba-Montoya, A. Wilkins, Z. Yang and A. D. Yoder, *Using phylogenomic data to explore the effects of relaxed clocks and calibration strategies on divergence time estimation: primates as a test case*, Systematic Biology (2018). <https://doi.org/10.1093/sysbio/syy001> (PMCID: PMC6005039). Methods: "Rate Prior", "MCMC and Bayesian Selection of Clock Model", "Effect of Genome-Scale Data"; Results: "Effect of Genome-Scale Data" (Figure 6); Discussion: "Clock Model".
- B. Rannala and Z. Yang, *Inferring speciation times under an episodic molecular clock*, Systematic Biology (2007).
