# Reproduction number of the opioid use disorder model with treatment and relapse cycling

Model illicit opioid use disorder (OUD) as a contagion in a population $N = S + I + T + R$ of susceptibles $S$, people with illicit OUD $I$, people in specialty treatment $T$, and recovered people $R$:

$$\begin{aligned}
S' &= \Lambda - \beta S\frac{I}{N} - \mu S,\\
I' &= \beta S\frac{I}{N} + \alpha_1 R + \alpha_2 R\frac{I}{N} + \kappa T - \frac{\eta_1 I + \eta_2 \frac{R}{N} I + \eta_3 \frac{S}{N} I}{1 + \epsilon T} - (\omega + \mu + \delta) I,\\
T' &= \frac{\eta_1 I + \eta_2 \frac{R}{N} I + \eta_3 \frac{S}{N} I}{1 + \epsilon T} - (\kappa + \rho + \mu) T,\\
R' &= \omega I + \rho T - (\alpha_1 + \mu) R - \alpha_2 R\frac{I}{N}.
\end{aligned}$$

Here $\Lambda$ is recruitment and $\mu$ natural death. $\delta$ is extra (overdose) death for $I$. $\eta_1$, $\eta_2$, $\eta_3$ are rates of entering treatment: spontaneous, prompted by recovered people, and prompted by susceptibles. The factor $1/(1 + \epsilon T)$ models saturated treatment capacity. $\kappa$ is relapse from treatment, $\rho$ completion of treatment, $\omega$ recovery without specialty treatment, and $\alpha_1$, $\alpha_2$ are spontaneous and contact-driven relapse from $R$. All parameters are nonnegative. The disorder-free equilibrium is $(\Lambda/\mu, 0, 0, 0)$, and $N' = \Lambda - \mu N - \delta I$.

**Reproduction number.** Treating $I$, $T$, $R$ as infected compartments, with only $\beta SI/N$ counted as new infections, the next-generation method gives

$$\mathcal R_0 = \frac{\beta}{D}\cdot\frac{1}{1 - r_1 - r_2 - r_3}, \qquad D = \mu + \delta + \eta_1 + \eta_3 + \omega,$$

$$r_1 = \frac{\eta_1 + \eta_3}{D}\cdot\frac{\kappa}{\kappa + \rho + \mu}, \qquad r_2 = \frac{\omega}{D}\cdot\frac{\alpha_1}{\alpha_1 + \mu}, \qquad r_3 = \frac{\eta_1 + \eta_3}{D}\cdot\frac{\rho}{\kappa + \rho + \mu}\cdot\frac{\alpha_1}{\alpha_1 + \mu}.$$

Equivalently,

$$\mathcal R_0 = \frac{\beta(\kappa + \rho + \mu)(\alpha_1 + \mu)}{(\kappa + \rho + \mu)(\alpha_1 + \mu)(\mu + \delta) + \mu\big[(\eta_1 + \eta_3)(\mu + \rho + \alpha_1) + \omega(\kappa + \rho + \mu)\big]} .$$

$\mathcal R_0$ does not depend on the contact-driven rates $\eta_2$ and $\alpha_2$ or on the saturation constant $\epsilon$. It decreases in $\eta_1$, $\eta_3$, $\omega$ and $\delta$, and increases in $\beta$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

Heuristically, a person with OUD spends mean time $1/D$ in $I$ per visit, causing $\beta/D$ new cases per visit. On leaving, they return to $I$ via treatment (probability $r_1$), via recovery and relapse ($r_2$), or via treatment, completion and relapse ($r_3$). The expected number of visits to $I$ is the geometric series $\sum_k (r_1 + r_2 + r_3)^k = 1/(1 - r_1 - r_2 - r_3)$. Formally, at the disorder-free state $S/N = 1$ and $R = T = 0$, so the terms in $\eta_2$, $\alpha_2$ and $\epsilon$ vanish from the Jacobian. Then $F$ has the single nonzero entry $\beta$, and $V$ is the $3 \times 3$ transfer matrix on $(I, R, T)$, so $\rho(FV^{-1}) = \beta\, (V^{-1})_{11}$. Expanding $(V^{-1})_{11}$ reproduces the cycle formula and its polynomial form, the denominator being $\det V$.

## Sources

- Cole S, Wirkus S. Modeling the dynamics of heroin and illicit opioid use disorder, treatment, and recovery. *Bulletin of Mathematical Biology* 84(4):48 (2022), model (1) and (6), subsection "Calculating the basic reproductive number", equations (7)–(8) and the next-generation matrices $F$, $V$. <https://doi.org/10.1007/s11538-022-01002-w> (PMCID: PMC8891131)
