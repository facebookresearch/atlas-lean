# Reproduction-number threshold for the SE(R)IRS model

**Model.** In a closed population of size $n$, susceptibles $S$ become exposed $E$ through contact with infectious individuals $I$ and with exposed individuals, who transmit at a reduced relative rate $\alpha \in [0,1]$. Exposed individuals either become infectious at rate $\sigma$ or recover directly (asymptomatic course) at rate $\delta$; infectious individuals recover at rate $\gamma$; immunity wanes at rate $\omega$:

$$\begin{aligned}
\dot S &= -\beta S(I + \alpha E)/n + \omega R, & \dot E &= \beta S(I + \alpha E)/n - (\sigma + \delta)E,\\
\dot I &= \sigma E - \gamma I, & \dot R &= \delta E + \gamma I - \omega R,
\end{aligned}$$

with all parameters positive.

**Theorem.** The basic reproduction number is

$$\mathfrak R_0 = \left(\frac{\alpha\gamma + \sigma}{\delta + \sigma}\right)\frac{\beta}{\gamma}.$$

If $\mathfrak R_0 < 1$, the disease-free equilibrium $(n,0,0,0)$ is locally asymptotically stable and no endemic equilibrium exists in the feasible region. If $\mathfrak R_0 > 1$, the disease-free equilibrium is unstable and the unique endemic equilibrium is locally asymptotically stable.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Proof depends on

- [Routh–Hurwitz criterion for cubic polynomials](../../../../Analysis/control-theory/feedback-stability-and-classical-design/routh-hurwitz-criterion-for-cubic-polynomials.md)
- [$R_0$ as a threshold for the linearized infected subsystem](../../next-generation-matrix-and-the-basic-reproductio/is-hurwitz-sub-iff-r0-lt-one.md)

## Expansion

With the infected compartments $(E, I)$, the next-generation matrices at the disease-free state are $F = \begin{pmatrix}\alpha\beta & \beta\\ 0 & 0\end{pmatrix}$ and $V = \begin{pmatrix}\sigma + \delta & 0\\ -\sigma & \gamma\end{pmatrix}$, and $\mathfrak R_0 = \rho(FV^{-1})$. Reading the formula: an exposed individual spends mean time $1/(\sigma+\delta)$ in $E$, infecting at rate $\alpha\beta$, and with probability $\sigma/(\sigma+\delta)$ becomes infectious and then infects at rate $\beta$ for mean time $1/\gamma$; the sum is $\frac{\beta}{\sigma+\delta}\big(\alpha + \frac{\sigma}{\gamma}\big)$. Waning immunity makes the endemic state an equilibrium rather than a transient, so herd immunity in this model means a stable endemic level, not eradication. Local stability of the endemic equilibrium follows from the Routh–Hurwitz conditions on the reduced three-dimensional system.

## Sources

- Monique Chyba, Taylor Klotz, Yuriy Mileyko and Corey Shanbrom, "A look at endemic equilibria of compartmental epidemiological models and model control via vaccination and mitigation", Mathematics of Control, Signals, and Systems 36 (2023), 297–327, <https://doi.org/10.1007/s00498-023-00365-2>; numbering as in arXiv:2109.01738: Proposition 1 and Theorem 2.
