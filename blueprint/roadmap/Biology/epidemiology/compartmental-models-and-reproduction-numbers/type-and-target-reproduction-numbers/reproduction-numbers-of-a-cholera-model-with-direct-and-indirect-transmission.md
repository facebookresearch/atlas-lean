# Reproduction numbers of a cholera model with direct and indirect transmission

**Model (Tien–Earn).** A constant human population $N = S + I + R$ with per-capita birth and death rate $d$, recovery rate $\gamma$, and a waterborne pathogen concentration $B$ shed at rate $\xi$ per infective and decaying at rate $\delta$:

$$\dot S = dN - b_B S B - b_I S I - dS,\quad \dot I = b_B S B + b_I S I - (d+\gamma) I,\quad \dot R = \gamma I - dR,\quad \dot B = \xi I - \delta B,$$

with all parameters positive and disease-free equilibrium $(N, 0, 0, 0)$. Write $\beta_I = b_I N$ and $\beta_B = b_B N \xi/\delta$.

**Proposition 1 (shedding as transition).** With $F = \begin{pmatrix} \beta_I & b_B N \\ 0 & 0\end{pmatrix}$ and $V = \begin{pmatrix} d+\gamma & 0 \\ -\xi & \delta\end{pmatrix}$ the next-generation matrix has rank one and

$$R_0 = \frac{\beta_B + \beta_I}{d+\gamma} = R_{0B} + R_{0I}, \qquad R_{0B} = \frac{\beta_B}{d+\gamma},\ R_{0I} = \frac{\beta_I}{d+\gamma}.$$

The elasticities are $\Upsilon_{\beta_B}^{R_0} = R_{0B}/R_0$, $\Upsilon_{\beta_I}^{R_0} = R_{0I}/R_0$ and $\Upsilon_{\gamma}^{R_0} = -\gamma/(d+\gamma)$.

**Proposition 2 (shedding as new infection).** With $\tilde F = \begin{pmatrix} b_I N & b_B N \\ \xi & 0\end{pmatrix}$, $\tilde V = \mathrm{diag}(d+\gamma, \delta)$, the next-generation matrix $\tilde K = \tilde F \tilde V^{-1}$ has rank two and $\tilde R_0 = \rho(\tilde K)$ is the unique positive root of

$$G(z) = z^2 - R_{0I}\, z - R_{0B}.$$

Since $G(1) = 1 - R_{0I} - R_{0B}$, $\tilde R_0 < 1 \iff R_0 < 1$, although $\tilde R_0 \ne R_0$ in general.

**Proposition 3 (target reproduction numbers for $\tilde K$).** Targeting direct transmission, $S = \{(1,1)\}$, gives $T_S = R_{0I}/(1 - R_{0B})$ when $R_{0B} < 1$. Targeting the water route, $S = \{(1,2)\}$, gives $T_S = R_{0B}/(1 - R_{0I})$ when $R_{0I} < 1$; then cutting a fraction greater than $(R_0 - 1)/R_{0B}$ of indirect transmission eliminates cholera.

## Depends on

- [Target reproduction number](target-reproduction-number.md)

## Expansion

In Proposition 1, $FV^{-1}$ has first row $\big(\beta_I/(d+\gamma) + b_B N\xi/(\delta(d+\gamma)),\ b_B N/\delta\big)$ and second row zero, so its only nonzero eigenvalue is its $(1,1)$ entry. In Proposition 2 the characteristic polynomial of $\tilde K = \begin{pmatrix} R_{0I} & b_B N/\delta \\ \xi/(d+\gamma) & 0\end{pmatrix}$ is $G$, whose coefficient signs force exactly one positive root. For Proposition 3 with $S = \{(1,2)\}$, $K_S$ has a single nonzero entry and $(I - K + K_S)^{-1}$ is triangular, giving $T_S = R_{0B}/(1 - R_{0I})$; requiring $(1-\varepsilon)T_S < 1$ gives $\varepsilon > (R_0 - 1)/R_{0B}$. Both splittings give the same threshold but only the rank-one splitting is additive in the two routes. For the 2006 Angola outbreak parameters quoted by the source ($\beta_B = 1.21$, $\beta_I = 0.264$, $\gamma = 0.25$ per day, $d \approx 0$), $R_{0B} = 4.84$, $R_{0I} = 1.05$, $R_0 = 5.89$.

## Sources

- P. van den Driessche, "Reproduction numbers of infectious disease models", Infectious Disease Modelling 2(3) (2017) 288–303, Section 6.1, <https://doi.org/10.1016/j.idm.2017.06.002> (PMC6002118).
- J. H. Tien and D. J. D. Earn, "Multiple transmission pathways and disease dynamics in a waterborne pathogen model", Bull. Math. Biol. 72 (2010) 1506–1533.
