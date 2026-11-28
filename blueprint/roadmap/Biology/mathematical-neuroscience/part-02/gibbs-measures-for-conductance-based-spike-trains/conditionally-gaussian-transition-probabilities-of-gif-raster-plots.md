# Conditionally Gaussian transition probabilities of generalized integrate-and-fire raster plots

Consider $N$ generalized integrate-and-fire (gIF) neurons. Below the firing threshold $\theta$ the membrane potentials obey

$$C_k \frac{dV_k}{dt} + g_k(t,\omega) V_k = i_k(t,\omega), \qquad k = 1, \dots, N,$$

with conductance $g_k(t,\omega) = g_{L,k} + \sum_{j} G_{kj}\,\alpha_{kj}(t,\omega)$ and current $i_k(t,\omega) = g_{L,k} E_L + \sum_j W_{kj}\,\alpha_{kj}(t,\omega) + i_k^{(ext)}(t) + \sigma_B \xi_k(t)$, where $\alpha_{kj}(t,\omega)$ is the summed synaptic response of $k$ to all past spikes of $j$, $W_{kj} = E^{\pm} G_{kj}$ with the reversal potential of $j$'s synapse type, and the $\xi_k$ are independent standard white noises, with $\sigma_B > 0$. When $V_k$ reaches $\theta$ the neuron spikes and is reset to a Gaussian value with mean 0 and variance $\sigma_R^2 > 0$, the reset values being independent of one another and of the noise. Time is discretized into unit bins and the raster is $\omega = (\omega_k(n))$ with $\omega_k(n) \in \{0, 1\}$; $\tau_k(t,\omega)$ denotes the last reset time of neuron $k$ before $t$, and $\omega_{-\infty}^{n-1}$ is the whole past raster.

**Conditional law of the potential.** Conditionally on the past raster $\omega_{-\infty}^{[t]}$, the vector $V(t)$ is Gaussian, its components are conditionally independent, $\mathbb{E}[V_k(t) \mid \omega] = V_k^{(det)}(\tau_k(t,\omega), t, \omega)$ (the noiseless solution started at the last reset), and $\operatorname{Var}[V_k(t) \mid \omega] = \sigma_k^2(\tau_k(t,\omega), t, \omega)$, the sum of the integrated white-noise variance and the propagated reset variance.

**Transition probabilities.** Consequently

$$P[\omega(n) \mid \omega_{-\infty}^{n-1}] = \prod_{k=1}^{N} \Big( \omega_k(n)\,\pi\big(X_k(n-1,\omega)\big) + (1 - \omega_k(n))\big(1 - \pi(X_k(n-1,\omega))\big) \Big),$$

where

$$X_k(n-1,\omega) = \frac{\theta - V_k^{(det)}(\tau_k(n-1,\omega), n-1, \omega)}{\sigma_k(\tau_k(n-1,\omega), n-1, \omega)}, \qquad \pi(x) = \frac{1}{\sqrt{2\pi}} \int_x^{\infty} e^{-u^2/2}\,du.$$

Because the conductance carries the entire spike history and is not erased by the reset, these transition probabilities have unbounded memory: the raster is not a Markov chain of any finite order but a chain with complete connections, i.e. a family of transition kernels $P_n[\,\cdot \mid \omega_{-\infty}^{n-1}]$ together with any probability measure on rasters consistent with them.

## Expansion

Between resets the gIF equation is linear in $V_k$ with a raster-dependent coefficient, so it is solved by the integrating factor $\Gamma_k(t_1, t, \omega) = \exp\!\big(-\tfrac{1}{C_k}\int_{t_1}^{t} g_k\big)$. The noise enters additively, so the potential is the deterministic part plus a Wiener integral of $\Gamma_k$ plus the propagated reset noise, which is Gaussian; independence of the $B_k$ and of the reset values gives the diagonal covariance. A spike in bin $n$ is the event $V_k \ge \theta$, whose conditional probability is the Gaussian tail $\pi(X_k)$. The variance is bounded below by a positive constant, so $X_k$ is always defined.

## Sources

- B. Cessac, Statistics of spike trains in conductance-based neural networks: Rigorous results, Journal of Mathematical Neuroscience 1 (2011), Sections 3.6 and 7.1 to 7.3 (Propositions 7 and 8, Definition 3). <https://doi.org/10.1186/2190-8567-1-8> PMCID: PMC3496623
