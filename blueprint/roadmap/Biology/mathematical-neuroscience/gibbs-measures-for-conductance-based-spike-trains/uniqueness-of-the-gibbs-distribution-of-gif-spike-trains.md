# Uniqueness of the Gibbs distribution of gIF spike trains

Let $p(n,\omega) = P[\omega(n) \mid \omega_{-\infty}^{n-1}]$ be the transition probabilities of the generalized integrate-and-fire network with conductance-based synapses and Gaussian noise (see the dependency below). A probability measure $\mu$ on rasters is a Gibbs measure for $p$ if it is consistent with $p$ (for every $n$ and every $\mathcal{F}_{\le n}$-measurable $f$, $\int f\,d\mu = \int \sum_{\omega(n)} f(\omega_{-\infty}^{n-1}\omega(n))\,p(n,\omega)\,d\mu$) and the system $p$ is continuous and non-null.

**Theorem.** For every admissible choice of the network parameters, the gIF model has exactly one Gibbs distribution.

**Uniqueness criterion used (Fernandez-Maillard).** Let $m(p) = \inf_{n}\inf_{\omega} p(n,\omega)$ and $v(p) = \sup_{m'} \sum_{n \ge m'} \operatorname{var}_{n - m'}[p(n,\cdot)]$, where $\operatorname{var}_m[f] = \sup\{|f(\omega) - f(\omega')| : \omega, \omega' \text{ agree on the last } m \text{ time steps}\}$. If $m(p) > 0$ and $v(p) < \infty$, there is at most one Gibbs measure consistent with $p$.

**Corollary (exponential silence bound).** There are constants $0 < \Pi_- < \Pi_+ < 1$, depending only on the parameters, such that for $t - s > 1$ the probability under the Gibbs measure that neuron $k$ emits no spike in $[s, t]$ lies strictly between $\Pi_-^{[t]-[s]}$ and $\Pi_+^{[t]-[s]}$.

## Depends on

- [Conditionally Gaussian transition probabilities of gIF raster plots](conditionally-gaussian-transition-probabilities-of-gif-raster-plots.md)

## Expansion

Existence follows from the general fact that a continuous system of transition probabilities on the compact raster space admits a consistent measure; continuity in $\omega$ comes from continuity of the deterministic potential $V_k^{(det)}$ and of $\sigma_k$ with respect to the raster. Non-nullness: the conductances and potentials are uniformly bounded and $\sigma_k$ is bounded away from zero, so $X_k$ lies in a fixed compact interval and $\pi(X_k)$ in a fixed interval $(\pi_k^-, \pi_k^+) \subset (0,1)$; hence $m(p) \ge \prod_k \min(\pi_k^-, 1 - \pi_k^+) > 0$. Summable variation: the influence of spikes $m$ steps in the past on $V_k^{(det)}$ and $\sigma_k$ decays exponentially in $m$ (the synaptic responses decay and the leak contracts), so $\operatorname{var}_m[p(n,\cdot)]$ is exponentially small and $v(p) < \infty$. The silence bound follows by chaining the one-step bounds on $P[\omega_k(n) = 0 \mid \text{past}]$. The unique Gibbs measure is in general non-stationary and its potential has infinite range, which is why finite-range maximum-entropy models of spike trains are approximations to it.

## Sources

- B. Cessac, Statistics of spike trains in conductance-based neural networks: Rigorous results, Journal of Mathematical Neuroscience 1 (2011), Sections 6, 7.4 and 8.1 (Propositions 4 to 6, Theorem 1, Propositions 9 and 10). <https://doi.org/10.1186/2190-8567-1-8> PMCID: PMC3496623
