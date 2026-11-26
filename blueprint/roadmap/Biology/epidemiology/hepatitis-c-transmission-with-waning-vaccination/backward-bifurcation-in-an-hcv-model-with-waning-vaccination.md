# Backward bifurcation in a hepatitis C transmission model with waning vaccination

**Model.** A population with recruitment $\Lambda$ and death rate $\mu$ is divided into susceptible $S$, exposed $E$, acutely infected $I$, treated $T$, chronically infected $C_h$ and vaccinated $V$ individuals. A fraction $b$ of recruits is vaccinated; vaccine protection wanes at rate $\alpha$ and has efficacy $\psi \in (0,1]$. With force of infection $\lambda = \beta_1 I + \beta_2 C_h + \beta_3 T$,

$$

\begin{aligned}
S' &= (1-b)\Lambda + \rho T + \alpha V - \lambda S + \sigma C_h - \mu S, &
E' &= \lambda S + (1-\psi)\lambda V - (\epsilon + \mu)E,\\
I' &= \epsilon E - (\kappa + \mu)I, &
T' &= \pi_1\kappa I + \pi_2 C_h - (\rho + \mu)T,\\
C_h' &= (1-\pi_1)\kappa I - (\pi_2 + \sigma + \mu)C_h, &
V' &= b\Lambda - (\alpha + \mu)V - (1-\psi)\lambda V,
\end{aligned}

$$

where $\epsilon$ is the rate of progression to acute infection, $\kappa$ the rate of leaving the acute stage (a fraction $\pi_1$ to treatment), $\pi_2$ the treatment rate of chronic cases, and $\rho$, $\sigma$ the recovery rates from treatment and from chronic infection. Put $K_1 = \epsilon + \mu$, $K_2 = \kappa + \mu$, $K_3 = \rho + \mu$, $K_4 = \pi_2 + \sigma + \mu$, $K_5 = \alpha + \mu$ and

$$

B = \beta_1 + \beta_2\frac{\kappa(1-\pi_1)}{K_4} + \beta_3\frac{\pi_1\kappa K_4 + \pi_2\kappa(1-\pi_1)}{K_3K_4}.

$$

**Theorem (threshold).** The disease-free equilibrium is $P_0 = (S_0, 0, 0, 0, 0, V_0)$ with $S_0 = \frac{(1-b)\Lambda}{\mu} + \frac{\alpha b\Lambda}{\mu K_5}$ and $V_0 = \frac{b\Lambda}{K_5}$, and

$$

R_0 = \frac{\epsilon B}{K_1K_2}\big(S_0 + (1-\psi)V_0\big).

$$

$P_0$ is locally asymptotically stable if $R_0 < 1$ and unstable if $R_0 > 1$.

**Theorem (endemic equilibria).** Endemic equilibria correspond to positive roots $I^*$ of $a_1 I^{*2} + a_2 I^* + a_3 = 0$, where $a_1 > 0$ for an imperfect vaccine ($\psi < 1$) and $a_3 = \mu K_1K_2K_3K_4K_5(1 - R_0)$. The model has a unique endemic equilibrium if $R_0 > 1$; a unique one if $a_2 < 0$ and either $a_3 = 0$ or $a_2^2 = 4a_1a_3$; two endemic equilibria if $a_3 > 0$ (that is, $R_0 < 1$), $a_2 < 0$ and $a_2^2 > 4a_1a_3$; and none otherwise. In the two-equilibrium regime a stable disease-free equilibrium coexists with a stable endemic equilibrium below $R_0 = 1$ (backward bifurcation, confirmed by a Castillo-Chavez–Song bifurcation analysis with $\beta_1$ as bifurcation parameter), so pushing $R_0$ below one need not eliminate HCV.

**Theorem (perfect vaccine).** For $\psi = 1$ one has $a_1 = 0$ and $a_2 > 0$, so no endemic equilibrium exists when the vaccinated reproduction number $\bar R_0 = R_0|_{\psi = 1} = \epsilon B S_0/(K_1K_2) \le 1$: a perfect vaccine removes the backward bifurcation, and $P_0$ is globally asymptotically stable whenever $\bar R_0 \le S_0\mu/\Lambda < 1$. Without recovery ($\rho = \sigma = 0$), the endemic equilibrium is globally asymptotically stable whenever it exists.

## Depends on

- [$R_0$ as a threshold for the linearized infected subsystem](../next-generation-matrix-and-the-basic-reproductio/is-hurwitz-sub-iff-r0-lt-one.md)

## Expansion

The next-generation construction on $(E, I, T, C_h)$ gives $R_0$ as transmission per unit time $B$ (accumulated over the acute, treated and chronic stages) times the mean exposed-to-acute passage $\epsilon/(K_1K_2)$, times the effective susceptible pool, in which vaccinees count with weight $1-\psi$. At equilibrium every infected compartment is proportional to $I^*$ and the vaccinated class is a decreasing function of $I^*$, which produces the quadratic. When $R_0 < 1$ but $a_2 < 0$, infection of partially protected vaccinees supplies the positive feedback behind two positive roots. With a perfect vaccine the vaccinated class is decoupled, the quadratic term vanishes and only the nonpositive root $-a_3/a_2$ remains.

## Sources

- Daniah Tahir, Abid Ali Lashari, Kazeem Oare Okosun, *Analysis of a model for hepatitis C virus transmission that includes the effects of vaccination with waning immunity*, arXiv 2017. Theorem 2.1 (local stability of the DFE), Theorem 2.2 (endemic equilibria), Theorem 2.3 (perfect vaccine), Theorem 2.4 (global stability of the endemic equilibrium); Section 2. <https://doi.org/10.48550/arXiv.1712.08548>
