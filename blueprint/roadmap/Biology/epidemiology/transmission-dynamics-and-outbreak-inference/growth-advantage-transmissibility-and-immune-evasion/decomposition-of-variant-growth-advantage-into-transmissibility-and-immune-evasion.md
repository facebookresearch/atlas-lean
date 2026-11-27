# Decomposition of a variant's growth advantage into transmissibility and immune evasion

Consider a resident (wild-type) variant with transmission rate $\beta > 0$ in a population where a fraction $S \in (0, 1]$ is susceptible to it, and a new variant whose intrinsic transmissibility is higher by a factor $1 + \tau$ ($\tau > -1$) and which evades a fraction $\epsilon \in [0, 1]$ of the protective immunity against the resident variant. If both variants are removed at the same rate, the difference of their per-capita net growth rates, the growth advantage, is

$$\rho = (1 + \tau)\, \beta \big(S + \epsilon (1 - S)\big) - \beta S.$$

Let $D > 0$ be the generation time, $R_w = \beta S D$ the effective reproduction number of the resident variant, and $\Omega = 1 - S$ the immune fraction. Then

$$\frac{\rho D}{R_w} = (1 + \tau)\Big(1 + \epsilon \frac{\Omega}{1 - \Omega}\Big) - 1,$$

and for $\Omega \in (0, 1)$ this can be solved for either mechanism given the other:

$$\epsilon = \frac{1 - \Omega}{\Omega} \Big(\frac{1 + \rho D / R_w}{1 + \tau} - 1\Big), \qquad 1 + \tau = \frac{1 + \rho D / R_w}{1 + \epsilon\, \Omega / (1 - \Omega)}.$$

Consequences, for fixed $\rho > 0$, $D$, $R_w$ and $\Omega \in (0, 1)$:

1. Immune evasion and the transmissibility increase trade off: $\epsilon$ is strictly decreasing in $\tau$.
2. With no change in intrinsic transmissibility ($\tau = 0$), $\epsilon = (1 - \Omega)\rho D / (\Omega R_w)$; with no immune evasion ($\epsilon = 0$), $\tau = \rho D / R_w$.
3. A pair $(\tau, \epsilon)$ is admissible ($\epsilon \le 1$) if and only if $1 + \tau \ge (1 - \Omega)(1 + \rho D / R_w)$.
4. For a fixed $\tau$ with $1 + \tau < 1 + \rho D / R_w$ (so that some evasion is required), the evasion needed to explain the advantage decreases as population immunity $\Omega$ increases.

## Proof sketch

Under susceptible–infected–recovered dynamics with shared removal rate $\gamma$, the resident grows at $\beta S - \gamma$ and the new variant at $(1 + \tau)\beta(S + \epsilon(1 - S)) - \gamma$, since it can also infect the evaded share of the immune; subtracting cancels $\gamma$. Dividing by $\beta S = R_w / D$ and writing $(1 - S)/S = \Omega/(1 - \Omega)$ gives the normalized identity, which is linear in $\epsilon$ and in $1 + \tau$, hence the explicit solutions and the monotonicity. For Omicron BA.1 against Delta in Gauteng, South Africa, a multinomial logistic regression on 805 sequences gave $\rho = 0.24$ per day (95% CI 0.16–0.33), a 5.4-fold weekly increase relative to Delta; with $D \sim \mathcal{N}(5.2, 0.8^2)$ days and $R_w$ between 0.78 and 0.85, the inferred immune evasion depends strongly on the assumed $\Omega$ and $\tau$, so growth data alone cannot separate the two mechanisms.

## Sources

- R. Viana et al., "Rapid epidemic expansion of the SARS-CoV-2 Omicron variant in southern Africa", Nature 603 (2022), 679–686, Methods (growth advantage and its relationship to transmissibility and immune evasion) and Fig. 4, <https://doi.org/10.1038/s41586-022-04411-y>, PMCID: PMC8942855.
