# Settling guarantee

Let $\Omega$ be a measurable space and $\iota$ an index set of observations. Given thresholds $V_{il}, V_{ih}$, output levels $V_{ol}, V_{oh}$, and for each $i$ a resolution time $\tau_i(\omega)$, a budget $b_i$, an ideal voltage $V_i(\omega)$, a noise $n_i(\omega)$, an observed voltage $V^{\mathrm{obs}}_i(\omega)$ and an expected bit $\beta_i(\omega)$, the settling guarantee holds when, for every $i$ and $\omega$:

- $V^{\mathrm{obs}}_i(\omega) = V_i(\omega) + n_i(\omega)$;
- if $\tau_i(\omega) \le b_i$, then either $\beta_i(\omega)$ is false and $V_i(\omega) \le V_{ol}$, or $\beta_i(\omega)$ is true and $V_{oh} \le V_i(\omega)$;
- if $\tau_i(\omega) \le b_i$, then $|n_i(\omega)| < \min(V_{il} - V_{ol},\, V_{oh} - V_{ih})$.
