# Seasonally forced SIRS model with vital dynamics

Let $S, I, R \ge 0$ be the numbers of susceptible, infectious and recovered individuals in a population of constant size $N = S + I + R$. Births enter $S$ at rate $\mu N$, every compartment dies at per-capita rate $\mu > 0$, infectious individuals recover at rate $\nu > 0$, and immunity wanes at rate $\gamma \ge 0$. Transmission is mass action with the periodic rate

$$\beta(t) = b_0\bigl(1 + b_1\cos(2\pi t - \phi)\bigr), \qquad b_0 > 0,\ 0 \le b_1 < 1,\ \phi \in \mathbb{R},$$

with time in years. The model is

$$\dot S = \mu N - \frac{\beta(t)SI}{N} - \mu S + \gamma R, \qquad \dot I = \frac{\beta(t)SI}{N} - (\nu+\mu)I, \qquad \dot R = \nu I - (\gamma+\mu)R .$$

Then $S + I + R$ is constant. In the unforced case $b_1 = 0$, with $\mathcal{R}_0 = b_0/(\nu+\mu)$, the disease-free state $(N, 0, 0)$ is always an equilibrium. When $\mathcal{R}_0 > 1$ there is a unique endemic equilibrium

$$S^* = \frac{N}{\mathcal{R}_0}, \qquad I^* = N\Bigl(1 - \frac{1}{\mathcal{R}_0}\Bigr)\frac{\gamma+\mu}{\nu+\gamma+\mu}, \qquad R^* = \frac{\nu}{\gamma+\mu}\,I^* .$$

The M-SEIRS4 refinement splits susceptibles by the number of past infections ($S_1,\dots,S_4$, with relative susceptibilities $\tau_i$), adds latent classes entered at rate $\sigma$, weights infectiousness by $\eta_i$ (force of infection $\beta(t)\tau_i\sum_j \eta_j I_j/N$), and lets a fraction of births enter a maternally immune class.

## Depends on

- [Solution of the Kermack–McKendrick SIR system](../kermack-mckendrick-sir-model/is-solution.md)

## Expansion

Adding the three equations gives $\dot S + \dot I + \dot R = \mu N - \mu(S+I+R) = 0$ when $S + I + R = N$. For an equilibrium with $I^* > 0$, the $I$ equation forces $b_0S^*/N = \nu + \mu$, so $S^* = N/\mathcal{R}_0$. The $R$ equation gives $R^* = \nu I^*/(\gamma+\mu)$, and $S^* + I^* + R^* = N$ then gives $I^*$, which is positive exactly when $\mathcal{R}_0 > 1$. Substituting into the $S$ equation checks consistency: $\mu N(1 - 1/\mathcal{R}_0) = I^*\mu(\nu+\gamma+\mu)/(\gamma+\mu)$. Waning immunity ($\gamma > 0$) refills the susceptible pool much faster than births alone. Combined with seasonal forcing, it produces the annual or biennial epidemics that these models are fitted to.

## Sources

- J. C. Lang, *Use of mathematical modelling to assess respiratory syncytial virus epidemiology and interventions: a literature review*, Journal of Mathematical Biology 84 (2022), 26, <https://doi.org/10.1007/s00285-021-01706-y>, PMCID PMC8882104. Section "RSV disease state structure", Eq. (1) and the SIRS and M-SEIRS4 structures (after Weber et al. 2001).
