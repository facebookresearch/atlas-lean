# Seasonal brucellosis model with livestock vaccination

**Model.** Sheep/cattle are susceptible $S$, exposed $E$, infected $I$ or vaccinated $V$; humans are susceptible $S_h$, acutely infected $I_{ha}$ or chronically infected $I_{hc}$. With seasonal transmission rates $\beta(t) = \alpha[1 + b\sin(\frac{\pi}{2}t + c)]$ (livestock to livestock) and $\beta_h(t) = \alpha_h[1 + b_h\sin(\frac{\pi}{2}t + c_h)]$ (livestock to humans), period $\omega = 4$ (time in seasons),

$$\begin{aligned}
\dot S &= A - \beta(t) S (E + I) - (\mu + \nu) S + \delta V, & \dot S_h &= B - \beta_h(t) S_h (E + I) + \omega_h\eta I_{ha} - \mu_1 S_h,\\
\dot E &= \beta(t)(S + \epsilon V)(E + I) - (\lambda + \mu) E, & \dot I_{ha} &= \beta_h(t) S_h (E + I) - \omega_h I_{ha} - \mu_1 I_{ha},\\
\dot I &= \lambda E - (\mu + f) I, & \dot I_{hc} &= \omega_h(1-\eta) I_{ha} - \mu_1 I_{hc},\\
\dot V &= \nu S - (\mu + \delta) V - \epsilon\beta(t) V (E + I), & &
\end{aligned}$$

with livestock recruitment $A$, vaccination rate $\nu$, vaccine waning $\delta$, vaccine failure factor $\epsilon$, progression $\lambda$, natural death $\mu$ and culling of infected animals $f$; both exposed and infected animals transmit, and humans do not transmit (dead-end hosts).

**Results.**

1. The livestock subsystem $(S, E, I, V)$ is autonomous of the human equations and has the disease-free equilibrium $P_0 = (S^*, 0, 0, V^*)$ with

    $$S^* = \frac{A(\mu + \delta)}{\mu(\mu + \nu + \delta)}, \qquad V^* = \frac{A\nu}{\mu(\mu + \nu + \delta)},$$

    which is globally asymptotically stable for the infection-free linear system (eigenvalues $-\mu$ and $-(\mu + \nu + \delta)$).
    2. With $F(t) = \beta(t)(S^* + \epsilon V^*)\begin{pmatrix}1 & 1\\ 0 & 0\end{pmatrix}$ and $V = \begin{pmatrix}\lambda + \mu & 0\\ -\lambda & \mu + f\end{pmatrix}$ on $(E, I)$, the basic reproduction number is $\mathcal{R}_0 = \rho(L)$ for the periodic next-generation operator $L$.
    3. $P_0$ is globally asymptotically stable if $\mathcal{R}_0 < 1$ and unstable if $\mathcal{R}_0 > 1$.

## Depends on

- [Next-generation operator in a periodic environment](../../next-generation-matrix-and-the-basic-reproductio/periodic-next-generation-operator.md)

## Proof depends on

- [Local stability of the disease-free periodic solution](../../next-generation-matrix-and-the-basic-reproductio/local-stability-of-the-disease-free-periodic-solution.md)

## Expansion

If $\beta$ were constant, $\mathcal{R}_0 = \beta(S^* + \epsilon V^*)\big(\frac{1}{\lambda + \mu} + \frac{\lambda}{(\lambda + \mu)(\mu + f)}\big)$, the sum of transmission during the exposed and infected stages; vaccination lowers the effective susceptible pool from $A/\mu$ to $S^* + \epsilon V^*$. With seasonal forcing the threshold is the spectral radius of the periodic operator rather than this formula with the averaged rate. Global stability follows the Floquet comparison argument: livestock $S, V$ eventually lie below $S^* + \eta, V^* + \eta$, the $(E, I)$ subsystem is then bounded by a cooperative irreducible periodic linear system whose principal Floquet exponent is negative when $\mathcal{R}_0 < 1$, and $E, I \to 0$. Because humans are dead-end hosts, human brucellosis control reduces to reducing $\mathcal{R}_0$ in livestock (vaccination, culling, lowering $\alpha$), with human incidence tracking $\beta_h(t)(E + I)$.

## Sources

- P. Lou, L. Wang, X. Zhang, J. Xu, K. Wang, "Modelling Seasonal Brucellosis Epidemics in Bayingolin Mongol Autonomous Prefecture of Xinjiang, China, 2010–2014", BioMed Research International (2016) 5103718, Section 2 (models (1)–(4), equation (3), Lemmas 1–2, matrices (10)) and Section 3 (Theorem 4), <https://doi.org/10.1155/2016/5103718>.
