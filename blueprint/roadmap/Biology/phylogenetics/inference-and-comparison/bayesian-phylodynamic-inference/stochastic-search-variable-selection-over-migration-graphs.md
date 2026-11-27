# Stochastic search variable selection over migration graphs

Take the [discrete-trait phylogeographic chain](discrete-trait-ctmc-model-of-phylogeographic-diffusion.md) on $K$ sites with reversible generator $\Lambda_{ab} = \mu\, s_{ab}\, \pi_b$. Augment the state space with binary indicators $\delta_{ab} = \delta_{ba} \in \{0,1\}$, one per unordered pair $\{a,b\}$, $a \ne b$, and set

$$\Lambda_{ab} \;=\; \mu\, \delta_{ab}\, \theta_{ab}\, \pi_b \quad (a \ne b),$$

so that $\delta_{ab} = 0$ forces the rate to zero and deletes the edge $\{a,b\}$ from the migration graph $\mathcal{G}(\delta)$, while $\delta_{ab} = 1$ retains it with magnitude $\theta_{ab} > 0$. There are $E = K(K-1)/2$ such edges.

**Prior.** The indicators are a priori independent Bernoulli variables with small success probability $q$, so $\sum_{a<b} \delta_{ab}$ is binomial with $E$ trials; in the limit $q \to 0$, $E \to \infty$ with $Eq \to \lambda$ fixed, this collapses to a Poisson law on the number of edges,

$$p\bigl(\textstyle\sum_{a<b}\delta_{ab} = v\bigr) \;\propto\; \frac{\lambda^{v} e^{-\lambda}}{v!},$$

truncated to configurations whose graph $\mathcal{G}(\delta)$ is connected, since a disconnected chain cannot move a lineage between all sites. The mean $\lambda$ is chosen so that the prior places probability $1/2$ on the minimal connected configuration, which has $K-1$ edges. Conditional on the indicators, the unnormalized rates $\theta_{ab}$ are independent with a gamma prior of mean $\alpha/\beta$ and variance $\alpha/\beta^{2}$; the common default takes shape $\alpha = 1$, that is independent exponential rates. Either $\pi_a \equiv 1/K$ is fixed, expressing no long-run spatial preference, or $\pi$ is estimated with a flat prior. A distance-informed variant instead sets the prior means of the $\theta_{ab}$ to decrease with the geographic distance between the centroids of sites $a$ and $b$.

**Inference.** Markov chain Monte Carlo explores $(\delta, \theta, \pi, \mu, \tau, \theta_{\mathrm{clock}})$ jointly, with random-walk kernels on the continuous coordinates and a bit-flip kernel on $\delta$.

## Depends on

- [Discrete-trait continuous-time Markov chain model of phylogeographic diffusion](discrete-trait-ctmc-model-of-phylogeographic-diffusion.md)

## Remarks

The construction is the phylogenetic translation of variable selection in regression, where indicators switch predictors in and out and the posterior averages over models rather than selecting one by a deterministic search over all $2^{E}$ subsets. The difference from the regression setting is the sign constraint: regression coefficients are real and are shrunk toward zero by a prior whose variance vanishes with the indicator, whereas rates are nonnegative, so the indicator multiplies the rate instead of scaling a normal prior variance.

The prior does the work that the data cannot. With $K$ sites there are $K(K-1)/2$ rates and effectively one character, so most pairs of sites are never observed to exchange lineages; under a dense model those rates are not driven to zero but to poorly determined small values, which propagates into the ancestral reconstructions. Concentrating prior mass on sparse connected graphs, with half the mass at the minimum $K-1$ edges, encodes the expectation that geographic spread follows a few routes and leaves the data to add edges only when they are supported.

Truncating to connected graphs is not cosmetic: an unconnected graph makes the chain reducible, the stationary distribution $\pi$ no longer unique, and the normalization $-\sum_a \pi_a \Lambda_{aa} = 1$ ill-posed. The by-product of the scheme is interpretive: the posterior mean of $\delta_{ab}$ is the posterior probability that a route exists, which is directly what a migration hypothesis asks about.

## Sources

- P. Lemey, A. Rambaut, A. J. Drummond, M. A. Suchard, "Bayesian phylogeography finds its roots", PLoS Computational Biology 5(9) (2009) e1000520, Methods, "Bayesian stochastic search variable selection", "Prior specification" (Equation (4)) and "Distance informed prior" (Equation (5)), <https://doi.org/10.1371/journal.pcbi.1000520> (PMC2740835).
