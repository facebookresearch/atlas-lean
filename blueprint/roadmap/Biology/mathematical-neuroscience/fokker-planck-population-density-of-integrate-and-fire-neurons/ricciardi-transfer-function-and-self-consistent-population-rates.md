# Ricciardi transfer function and self-consistent population rates

Under the hypotheses of the Fokker–Planck description of a population of leaky integrate-and-fire neurons (time constant $\tau > 0$, leak $V_L$, threshold $\theta$, reset $V_r < \theta$, refractory period $t_{\mathrm{ref}} \ge 0$, Ornstein–Uhlenbeck input with constant drift $\mu$ and noise intensity $\sigma > 0$), the stationary population firing rate is

$$Q = \phi(\mu, \sigma) = \Big[t_{\mathrm{ref}} + \tau \sqrt{\pi} \int_{(V_r - V_L - \mu)/\sigma}^{(\theta - V_L - \mu)/\sigma} e^{u^2} \big(1 + \operatorname{erf}(u)\big)\, du\Big]^{-1}.$$

The function $\phi$ is the population transfer function of Ricciardi; $1/\phi - t_{\mathrm{ref}}$ is the mean first-passage time of the Ornstein–Uhlenbeck process from $V_r$ to $\theta$ given by Siegert's formula. It is positive, bounded above by $1/t_{\mathrm{ref}}$ when $t_{\mathrm{ref}} > 0$, and strictly increasing in the mean drive $\mu$.

For a network partitioned into populations $i = 1, \dots, P$ whose neurons share input statistics and fire independently, with drift $\mu_i(Q_1, \dots, Q_P)$ and noise $\sigma_i(Q_1, \dots, Q_P)$ determined by the rates of the presynaptic populations, the stationary rates are the solutions of the self-consistency equations

$$Q_i = \phi\big(\mu_i(Q), \sigma_i(Q)\big), \qquad i = 1, \dots, P,$$

which are exactly the fixed points of the relaxation dynamics $\tau_i \dot Q_i = -Q_i + \phi(\mu_i(Q), \sigma_i(Q))$, $\tau_i > 0$; integrating these dynamics to a stable fixed point is a practical way to find a stationary state and to map bifurcations of the spiking network.

## Depends on

- [Siegert formula](../siegert-mean-first-passage-formula/integral-firing-time.md)

- [Fokker–Planck equation for a population of leaky integrate-and-fire neurons](fokker-planck-equation-for-a-population-of-leaky-integrate-and-fire-neurons.md)

## Proof sketch

Insert the stationary density into the normalization $\int_{-\infty}^\theta p\, dV + Q t_{\mathrm{ref}} = 1$. Exchanging the order of integration in $\int p\, dV$ and using $\int_{-\infty}^{u} e^{-x^2} dx = \frac{\sqrt{\pi}}{2}(1 + \operatorname{erf} u)$ turns the double integral into $Q\tau\sqrt{\pi} \int e^{u^2}(1 + \operatorname{erf} u)\, du$ over $[(V_r - V_L - \mu)/\sigma, (\theta - V_L - \mu)/\sigma]$, and solving the linear equation for $Q$ gives $\phi$. Increasing $\mu$ shifts both integration limits down while leaving their difference fixed, and the integrand is positive and increasing, so the integral decreases and $\phi$ increases. Fixed points of $\tau_i \dot Q_i = -Q_i + \phi_i$ are precisely the solutions of $Q_i = \phi_i$. Stability of a fixed point of the rate dynamics is a heuristic for stability of the corresponding asynchronous state; the full spiking network is then simulated at the selected parameters to confirm the dynamics.

## Sources

- G. Deco, V. K. Jirsa, P. A. Robinson, M. Breakspear and K. Friston, "The dynamic brain: from spiking neurons to neural masses and cortical fields", PLoS Computational Biology 4(8) (2008), e1000092, section "The mean-field model" (Equations 29–33), <https://doi.org/10.1371/journal.pcbi.1000092>, PMCID: PMC2519166.
- N. Brunel and V. Hakim, "Fast global oscillations in networks of integrate-and-fire neurons with low firing rates", Neural Computation 11 (1999), 1621–1671, <https://doi.org/10.1162/089976699300016179>.
