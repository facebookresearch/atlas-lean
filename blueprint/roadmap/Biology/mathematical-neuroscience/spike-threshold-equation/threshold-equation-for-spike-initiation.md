# Threshold equation for spike initiation

**Model.** A single-compartment neuron with membrane capacitance $C$, leak conductance $g_L > 0$ and reversal potential $E_L$, sodium channels with maximal conductance $g_{\mathrm{Na}} > 0$ and reversal potential $E_{\mathrm{Na}}$, and other (voltage-gated or synaptic) conductances $g_i \ge 0$ with reversal potentials $E_i$, satisfies

$$C\frac{dV}{dt} = g_L(E_L - V) + \sum_i g_i (E_i - V) + g_{\mathrm{Na}}\, P_a(V)\, h\, (E_{\mathrm{Na}} - V) + I .$$

Activation is instantaneous with Boltzmann curve $P_a(V) = \big(1 + e^{(V_a - V)/k_a}\big)^{-1}$ (half-activation $V_a$, slope factor $k_a > 0$), and the inactivation variable $h \in (0,1]$ and the conductances $g_i$ vary slowly compared with spike initiation. Below spike initiation ($V \ll V_a$) use $P_a(V) \approx e^{(V - V_a)/k_a}$ and $E_{\mathrm{Na}} - V \approx E_{\mathrm{Na}} - V_a$. Put $g_{\mathrm{tot}} = g_L + \sum_i g_i$ and $E^* = (g_L E_L + \sum_i g_i E_i)/g_{\mathrm{tot}}$.

**Theorem (threshold equation).** Under these approximations the membrane equation becomes

$$C\frac{dV}{dt} = g_{\mathrm{tot}}(E^* - V) + g_{\mathrm{tot}}\, k_a \exp\!\Big(\frac{V - \theta}{k_a}\Big) + I,$$

an exponential integrate-and-fire model with slope factor $k_a$ and threshold

$$\theta = V_a - k_a \log\frac{g_{\mathrm{Na}}(E_{\mathrm{Na}} - V_a)}{k_a\, g_L} + k_a \log\frac{g_{\mathrm{tot}}}{g_L} - k_a \log h .$$

$\theta$ is the unique voltage at which the current–voltage function $F(V) = g_{\mathrm{tot}}(E^* - V) + g_{\mathrm{tot}} k_a e^{(V - \theta)/k_a}$ satisfies $F'(\theta) = 0$: for constant inputs, $V$ escapes to a spike exactly when it passes the minimum of $F$. With only leak and sodium ($h = 1$, $g_i = 0$), $\theta = V_T := V_a - k_a\log\big(g_{\mathrm{Na}}(E_{\mathrm{Na}} - V_a)/(k_a g_L)\big)$.

## Expansion

With the exponential approximation the sodium current is $g_{\mathrm{Na}} h (E_{\mathrm{Na}} - V_a) e^{(V - V_a)/k_a}$; writing it as $g_{\mathrm{tot}} k_a e^{(V - \theta)/k_a}$ and solving for $\theta$ gives the formula, and $F'(V) = -g_{\mathrm{tot}} + g_{\mathrm{tot}} e^{(V-\theta)/k_a}$ vanishes only at $V = \theta$. The threshold depends on channel properties through $V_a$ and the log of the sodium density relative to the leak, and rises by $k_a$ per $e$-fold increase in total conductance or $e$-fold decrease in available sodium channels. This predicts higher thresholds in vivo (larger total conductance) than in vitro and a threshold that increases with depolarization through inactivation; since $k_a$ is 4–8 mV for neuronal sodium channels, the modulation is of that order per $e$-fold change.

## Sources

- J. Platkiewicz and R. Brette, *A threshold equation for action potential initiation*, PLoS Computational Biology (2010). <https://doi.org/10.1371/journal.pcbi.1000850> (PMCID: PMC2900290). Results: "The threshold equation", "Threshold dynamics"; Materials and Methods: "Membrane equation", "Exponential approximation", "Dynamic threshold".
- N. Fourcaud-Trocmé, D. Hansel, C. van Vreeswijk and N. Brunel, *How spike generation mechanisms determine the neuronal response to fluctuating inputs*, Journal of Neuroscience (2003).
