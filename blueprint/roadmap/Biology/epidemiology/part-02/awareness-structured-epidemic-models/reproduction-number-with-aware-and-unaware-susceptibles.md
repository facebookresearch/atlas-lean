# Reproduction number of an SEIR model with aware and unaware susceptibles

**Model.** In a closed population of size $N$ without demography, the compartments are aware susceptibles $S_a$, unaware susceptibles $S_u$, exposed $E$, asymptomatic infectious $A$, symptomatic infectious $I$, hospitalized with mild $H_m$ or severe $H_s$ disease, recovered $R$ and deceased $D$. All parameters are positive, $0 < k < 1$, and $0 < \alpha \le 1$ is the relative susceptibility of aware individuals:

$$\begin{aligned}
S_a' &= -\alpha \beta S_a \frac{\sigma A + I}{N} + v S_u, &
S_u' &= -\beta S_u \frac{\sigma A + I}{N} - v S_u,\\
E' &= \beta \frac{(\sigma A + I)(\alpha S_a + S_u)}{N} - \theta E, &
A' &= k \theta E - \eta_a A,\\
I' &= (1 - k)\theta E - q_1 I, &
H_m' &= \tau I + \psi H_s - q_2 H_m,\\
H_s' &= \rho I + \varphi H_m - q_3 H_s, &
R' &= \eta_a A + \eta_i I + \eta_{H_m} H_m + \eta_{H_s} H_s,
\end{aligned}$$

with $D' = \delta_i I + \delta_{H_s} H_s$, $q_1 = \eta_i + \tau + \rho + \delta_i$, $q_2 = \eta_{H_m} + \varphi$, $q_3 = \eta_{H_s} + \psi + \delta_{H_s}$. Hospitalized individuals are isolated and do not transmit.

**Disease-free equilibrium.** Since unaware susceptibles convert to aware at rate $v$, the only infection-free equilibrium is $S_a = N$, with every other compartment zero.

**Proposition.** The basic reproduction number given by the next-generation matrix is

$$\mathcal{R}_0 = \alpha \beta \left( \frac{\sigma k}{\eta_a} + \frac{1 - k}{q_1} \right),$$

and the disease-free equilibrium is locally asymptotically stable if $\mathcal{R}_0 < 1$ and unstable if $\mathcal{R}_0 > 1$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

Take infected states $(E, A, I)$; $H_m, H_s$ receive inflow but cannot infect, so they do not affect $\mathcal{R}_0$. At the equilibrium $(\alpha S_a + S_u)/N = \alpha$, so new infections are $F = \begin{pmatrix} 0 & \alpha\beta\sigma & \alpha\beta \\ 0 & 0 & 0 \\ 0 & 0 & 0 \end{pmatrix}$ and transitions are $V = \begin{pmatrix} \theta & 0 & 0 \\ -k\theta & \eta_a & 0 \\ -(1-k)\theta & 0 & q_1 \end{pmatrix}$. $F V^{-1}$ has rank one, and its only non-zero eigenvalue is the first row of $F$ applied to the first column of $V^{-1}$, namely $\alpha\beta\sigma \cdot k/\eta_a + \alpha\beta \cdot (1-k)/q_1$; stability follows from the van den Driessche–Watmough theorem. The awareness rate $v$ does not appear: at the equilibrium the population is already fully aware, so $v$ shapes the transient (how fast the effective susceptibility falls from $1$ towards $\alpha$ during an outbreak seeded in an unaware population) but not the invasion threshold. A threshold computed with $S_u(0) = N$ instead, $\beta(\sigma k/\eta_a + (1-k)/q_1)$, describes initial growth only while awareness spreads slowly compared with transmission ($v$ small).

## Sources

- S. S. Musa, S. Qureshi, S. Zhao, A. Yusuf, U. T. Mustapha, D. He, "Mathematical modeling of COVID-19 epidemic with effect of awareness programs", Infectious Disease Modelling 6 (2021) 448–460, Section 2.2 (model (1)), Section 3.1 (Equation (2), Theorem 3.1), <https://doi.org/10.1016/j.idm.2021.01.012> (PMC7889444).
