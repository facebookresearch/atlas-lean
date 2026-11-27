# Unique Gibbs measure of a noisy discrete-time integrate-and-fire network

**Model.** Consider $N$ neurons with membrane potentials $V_i$, firing threshold $\theta > 0$, firing indicator $Z(x) = \mathbb 1\{x \ge \theta\}$, leak $\gamma \in [0,1)$, bounded synaptic weights $W_{ij} \in [W_{\min}, W_{\max}]$ and constant inputs $I_i$, evolving synchronously in discrete time by

$$V_i(t+1) = \gamma V_i(t)\big(1 - Z[V_i(t)]\big) + \sum_{j=1}^N W_{ij}Z[V_j(t)] + I_i + \sigma_BB_i(t),$$

with i.i.d. standard Gaussian noise $B_i(t)$ and $\sigma_B > 0$: a neuron that fires is reset to zero and otherwise integrates leaky input. Given the past spike raster $\underline\omega = (\omega(s))_{s\le t}$, $\omega_i(s) \in \{0,1\}$, the potential is Gaussian with mean $C_i(\underline\omega)$ (inputs accumulated since the last spike of $i$) and standard deviation $\sigma_i(\underline\omega)$, so neuron $i$ spikes at time $t+1$ with probability $\pi\big((\theta - C_i(\underline\omega))/\sigma_i(\underline\omega)\big)$, where $\pi(x) = \frac{1}{\sqrt{2\pi}}\int_x^\infty e^{-u^2/2}du$.

**Theorem (uniqueness).** For all values of the parameters $W_{ij}$, $I_i$, $\gamma$, $\theta$ (and $\sigma_B > 0$), the spike-train process has a unique $g$-measure, i.e. a unique stationary law compatible with the transition probabilities $g_0(\omega) = \prod_i \big[\omega_i(0)\pi_i + (1 - \omega_i(0))(1 - \pi_i)\big]$.

**Theorem (Gibbs equilibrium state).** This measure $\mu_\psi$ is the equilibrium state of the potential

$$\psi(\underline\omega) = \log g_0(\underline\omega) = \sum_{i=1}^N\Big[\omega_i(0)\log\pi\Big(\frac{\theta - C_i(\underline\omega)}{\sigma_i(\underline\omega)}\Big) + \big(1 - \omega_i(0)\big)\log\Big(1 - \pi\Big(\frac{\theta - C_i(\underline\omega)}{\sigma_i(\underline\omega)}\Big)\Big)\Big],$$

so spike-train statistics are of Gibbs type with an infinite-range potential whose dependence on the past decays; finite-memory Markov approximations of this potential connect the model to the Gibbs (maximum-entropy) models used to analyse recorded spike trains.

## Proof sketch

Because the leak $\gamma < 1$ geometrically discounts old inputs and every spike resets the memory of the firing neuron, the dependence of $g_0$ on the distant past decays: the variations $\mathrm{var}_k(\log g_0)$ are summable (indeed square-summable), which is the Johansson–Öberg criterion for uniqueness of $g$-measures. Noise makes all transition probabilities strictly positive, which, together with this decay of memory, removes any dependence of the long-run statistics on initial conditions. Identifying the measure as an equilibrium state gives a variational principle (maximizing entropy plus average potential) and justifies Gibbs/maximum-entropy descriptions of neural data.

## Sources

- B. Cessac, "A discrete time neural network model with spiking neurons: II: Dynamics with noise", *Journal of Mathematical Biology* 62 (2011), 863–900, <https://doi.org/10.1007/s00285-010-0358-4>. Preprint version: arXiv:1002.3275 (2010), model definition and the theorems on uniqueness of the $g_0$-measure and its characterization as an equilibrium state, <https://doi.org/10.48550/arXiv.1002.3275>.
