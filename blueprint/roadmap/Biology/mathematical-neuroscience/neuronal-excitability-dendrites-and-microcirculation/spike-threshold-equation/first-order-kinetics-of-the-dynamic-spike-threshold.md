# First-order kinetics of the dynamic spike threshold

**Setting.** In the threshold equation with no conductances other than the leak, the instantaneous threshold is $\theta = V_T - k_a \log h$, where the sodium inactivation variable obeys Hodgkin–Huxley first-order kinetics

$$\tau_h(V)\frac{dh}{dt} = h_\infty(V) - h, \qquad 0 < h, h_\infty(V) \le 1 .$$

Define the steady-state threshold $\theta_\infty(V) = V_T - k_a \log h_\infty(V)$.

**Proposition.**

1. *(Exact threshold dynamics.)* Along any trajectory with $h > 0$,

$$\frac{d\theta}{dt} = \frac{k_a}{\tau_h(V)}\Big(1 - \exp\Big(\frac{\theta - \theta_\infty(V)}{k_a}\Big)\Big).$$

In particular $\theta$ increases when $\theta < \theta_\infty(V)$, decreases when $\theta > \theta_\infty(V)$, and is constant exactly when $\theta = \theta_\infty(V)$.
2. *(Linearization.)* If $|\theta - \theta_\infty(V)| \ll k_a$, then $\tau_h(V)\, \dfrac{d\theta}{dt} \approx \theta_\infty(V) - \theta$: the threshold relaxes to its steady state with the inactivation time constant.
3. *(Spike-triggered shift.)* If during a spike of duration $\Delta$ the equilibrium is $h_\infty \approx 0$ and the time constant averages $\bar\tau_h$, then $h \mapsto h\, e^{-\Delta/\bar\tau_h}$ and $\theta \mapsto \theta + k_a \Delta/\bar\tau_h$: each spike raises the threshold by a fixed amount.

## Depends on

- [Threshold equation for spike initiation](threshold-equation-for-spike-initiation.md)

## Expansion

Differentiating $\theta = V_T - k_a\log h$ gives $\dot\theta = -k_a \dot h/h = -\frac{k_a}{\tau_h}\big(\frac{h_\infty}{h} - 1\big)$. Inverting the two logarithmic relations, $h = e^{-(\theta - V_T)/k_a}$ and $h_\infty = e^{-(\theta_\infty - V_T)/k_a}$, so $h_\infty/h = e^{(\theta - \theta_\infty)/k_a}$, which is item 1; expanding $1 - e^{x} \approx -x$ for small $x = (\theta - \theta_\infty)/k_a$ gives item 2. For item 3, $h_\infty \approx 0$ reduces the kinetics to $\dot h = -h/\tau_h$ over the spike. The model thus predicts the time-varying threshold from the voltage trace and the inactivation properties, explains why the threshold correlates with the preceding membrane potential, and contributes to refractoriness through the per-spike shift.

## Sources

- J. Platkiewicz and R. Brette, *A threshold equation for action potential initiation*, PLoS Computational Biology (2010). <https://doi.org/10.1371/journal.pcbi.1000850> (PMCID: PMC2900290). Results: "The threshold equation", "Threshold dynamics"; Materials and Methods: "Membrane equation", "Exponential approximation", "Dynamic threshold".
