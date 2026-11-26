# Chain-binomial SEIR step with Poisson transmission

Fix a subpopulation (patch) of size $N$ with integer state $(S_t, E_t, I_t, R_t)$ on day $t$, a removal
rate $r > 0$ (inverse mean infectious period), a progression rate $\varepsilon > 0$ (inverse mean
latent period) and a daily transmitting-contact rate $c_t \ge 0$. One day of the stochastic model
draws, independently given the state,

$$\Delta R_t \sim \mathrm{Binomial}\bigl(I_t,\ 1 - e^{-r}\bigr), \qquad
\Delta I_t \sim \mathrm{Binomial}\bigl(E_t,\ 1 - e^{-\varepsilon}\bigr),$$

$$\Delta E_t \;=\; \min\Bigl\{S_t,\ \Bigl[\frac{S_t}{N} \sum_{m=1}^{I_t} Z_m\Bigr]\Bigr\}, \qquad Z_m \overset{\text{iid}}{\sim} \mathrm{Poisson}(c_t),$$

(new exposures are the Poisson offspring of the infectives thinned by the susceptible fraction,
with $[\cdot]$ denoting rounding) and updates
$S_{t+1} = S_t - \Delta E_t$, $E_{t+1} = E_t + \Delta E_t - \Delta I_t$,
$I_{t+1} = I_t + \Delta I_t - \Delta R_t$, $R_{t+1} = R_t + \Delta R_t$. For small daily
probabilities the conditional means of the increments are the one-day increments of the
deterministic SEIR system

$$\dot S = -\frac{c S I}{N}, \quad \dot E = \frac{c S I}{N} - \varepsilon E, \quad
\dot I = \varepsilon E - r I, \quad \dot R = r I,$$

whose basic reproduction number is $R_0 = c / r$. Accordingly the contact rate is calibrated as
$c = R_0 / D$, where $D = 1/r$ is the mean time from onset to isolation.

## Depends on

- [The SEIR vector field on ℝ⁴](../seir-epidemic-model/seir-field.md)
- [For β ≥ 0 and σ, γ > 0, the SEIR R₀ = ρ(F V⁻¹) equals β / γ](../seir-epidemic-model/r0-eq.md)

## Expansion

A compartment left at constant hazard $r$ is vacated within one day with probability
$1 - e^{-r} = r + O(r^2)$, so the binomial draws have conditional means
$I_t (1 - e^{-r}) \approx r I_t$ and $E_t (1 - e^{-\varepsilon}) \approx \varepsilon E_t$; the
thinned Poisson sum has mean $c_t I_t S_t / N$. These are the one-day Euler increments of the SEIR
field with $\beta = c$, $\sigma = \varepsilon$, $\gamma = r$, whose reproduction number is $\beta/\gamma$.
Interventions enter through time variation: contact reductions lower $c_t$, and faster case
isolation shortens $D$, which raises $r$. In the COVID-19 application $R_0 = 2.2$ and $D = 5.8$ days
at baseline, and the latent period was set from a 5.2-day incubation period. The source text prints
the daily progression probability with a typographical slip and omits the minus sign in
$\dot S$; the forms above are the consistent ones.

## Sources

- S. Lai, N. W. Ruktanonchai, L. Zhou et al., "Effect of non-pharmaceutical interventions to contain COVID-19 in China", *Nature* 585 (2020), <https://doi.org/10.1038/s41586-020-2293-x> (PMC7116778), Methods, "Data analysis", subsection "Exposure, infection, and recovery".
