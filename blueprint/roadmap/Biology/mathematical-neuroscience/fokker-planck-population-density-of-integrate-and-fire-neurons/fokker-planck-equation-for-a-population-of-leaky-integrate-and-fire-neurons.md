# Fokker–Planck equation for a population of leaky integrate-and-fire neurons

Consider $N$ leaky integrate-and-fire neurons with membrane time constant $\tau > 0$, leak potential $V_L$, threshold $\theta$, reset potential $V_r < \theta$ and refractory period $t_{\mathrm{ref}} \ge 0$, each receiving $\delta$-pulse synaptic input of efficacies $J$ from presynaptic spikes. In the mean-field and diffusion approximations (all neurons see inputs with the same statistics, many small kicks: $J \to 0$ with $N J^2$ fixed), the membrane potential of a neuron follows the Ornstein–Uhlenbeck dynamics

$$\tau \frac{dV}{dt} = -(V - V_L) + \mu(t) + \sigma(t) \sqrt{\tau}\, \xi(t)$$

between spikes, where $\xi$ is Gaussian white noise and the drift $\mu$ and noise intensity $\sigma^2$ are proportional to $\langle J \rangle N Q(t)$ and $\langle J^2 \rangle N Q(t)$, with $Q(t)$ the population firing rate. The density $p(V, t)$ of membrane potentials of non-refractory neurons then satisfies

$$\frac{\partial p}{\partial t} = \frac{\sigma^2}{2\tau} \frac{\partial^2 p}{\partial V^2} + \frac{\partial}{\partial V}\Big[\frac{V - V_L - \mu}{\tau}\, p\Big] + Q(t - t_{\mathrm{ref}})\, \delta(V - V_r), \qquad V < \theta,$$

equivalently $\partial_t p = -\partial_V \mathcal{F} + Q(t - t_{\mathrm{ref}})\delta(V - V_r)$ with probability flux $\mathcal{F} = -\frac{V - V_L - \mu}{\tau} p - \frac{\sigma^2}{2\tau} \partial_V p$, together with:

1. an absorbing threshold, $p(\theta, t) = 0$;
2. the firing rate equal to the flux through threshold, $Q(t) = \mathcal{F}(\theta, t) = -\frac{\sigma^2}{2\tau} \partial_V p(\theta, t)$;
3. integrability at $V \to -\infty$: $p$ and $V p$ vanish fast enough;
4. reinjection at reset after the refractory period (the delta source) and conservation of neurons, $\int_{-\infty}^{\theta} p(V, t)\, dV + \int_{t - t_{\mathrm{ref}}}^{t} Q(u)\, du = 1$.

The stationary solution, for constant $\mu, \sigma$ and rate $Q$, is

$$p(V) = \frac{2 Q \tau}{\sigma} \exp\Big(-\frac{(V - V_L - \mu)^2}{\sigma^2}\Big) \int_{(V - V_L - \mu)/\sigma}^{(\theta - V_L - \mu)/\sigma} H\Big(u - \frac{V_r - V_L - \mu}{\sigma}\Big)\, e^{u^2}\, du,$$

with $H$ the Heaviside function.

## Depends on

- [Period of the leaky integrate-and-fire neuron](../leaky-integrate-and-fire-neuron/lif-period.md)
- [Probability flux of a diffusion](../../../Probability/stochastic-calculus/fokker-planck-equation/flux.md)
- [Fokker–Planck operator](../../../Probability/stochastic-calculus/fokker-planck-equation/fokker-planck-op.md)

## Proof sketch

The population density evolves by the Chapman–Kolmogorov equation for the jump process of membrane potentials; a Taylor expansion of it is the Kramers–Moyal series, whose coefficients are the moments of the depolarization $dV$ in a short interval. The mean-field approximation replaces each neuron's input by the population rate $Q(t)$, so the first two moments are the drift and diffusion coefficients and all higher moments are of order $J^k N$, negligible in the diffusion limit; truncating at second order gives the Fokker–Planck equation of an Ornstein–Uhlenbeck process. Neurons leave through the threshold at rate $Q$ and are reinserted at $V_r$ after $t_{\mathrm{ref}}$, which produces the source term and the conservation law. In the stationary state the flux is $0$ below $V_r$ and $Q$ between $V_r$ and $\theta$; integrating the first-order equation $\mathcal{F} = Q\, H(V - V_r)$ with $p(\theta) = 0$ gives the stated solution. When $\sigma \to 0$ with $V_L + \mu > \theta$, the dynamics become deterministic and every neuron fires periodically with the deterministic integrate-and-fire period plus $t_{\mathrm{ref}}$.

## Sources

- G. Deco, V. K. Jirsa, P. A. Robinson, M. Breakspear and K. Friston, "The dynamic brain: from spiking neurons to neural masses and cortical fields", PLoS Computational Biology 4(8) (2008), e1000092, section "Mean-Field Models" (Equations 4–5, 9, 13–30), <https://doi.org/10.1371/journal.pcbi.1000092>, PMCID: PMC2519166.
- N. Brunel and V. Hakim, "Fast global oscillations in networks of integrate-and-fire neurons with low firing rates", Neural Computation 11 (1999), 1621–1671, <https://doi.org/10.1162/089976699300016179>.
