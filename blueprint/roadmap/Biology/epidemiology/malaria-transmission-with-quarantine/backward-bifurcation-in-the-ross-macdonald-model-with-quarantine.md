# Backward bifurcation in the Ross–Macdonald model with quarantine

**Model.** Humans (constant total $H$) are susceptible, infectious $I_h$ or quarantined $Q_h$; mosquitoes (constant total $V$, $m = V/H$) are susceptible or infectious $I_v$. Mosquitoes bite at constant rate $a$ (standard incidence), with transmission probabilities $b$ (mosquito to human) and $c$ (human to mosquito). A fraction $\theta$ of infectious humans is detected and quarantined at rate $\gamma_1$, the rest recover at rate $\gamma$; quarantined humans recover at rate $\gamma_2$ and receive a fraction $1 - \sigma$ of bites, $\sigma \in [0,1]$. Bites are redistributed to the non-quarantined population, giving

$$\begin{aligned}
I_h' &= ab\,\frac{I_v}{H - \sigma Q_h}\,(H - I_h - Q_h) - \big(\theta\gamma_1 + (1-\theta)\gamma\big) I_h,\\
Q_h' &= \theta \gamma_1 I_h - \gamma_2 Q_h,\\
I_v' &= ac\,\frac{I_h + (1-\sigma) Q_h}{H - \sigma Q_h}\,(V - I_v) - \mu I_v .
\end{aligned}$$

For $\theta = 0$ this is the classical Ross–Macdonald model with $\mathcal R_0 = \sqrt{a^2 b c m/(\gamma\mu)}$ and global threshold dynamics.

**Reproduction number.** The next-generation matrix gives

$$\mathcal R_{10} = \sqrt{\frac{a^2 b c m\,\big(\theta(1-\sigma)\gamma_1 + \gamma_2\big)}{\mu\,\gamma_2\,\big(\theta\gamma_1 + (1-\theta)\gamma\big)}} = \sqrt{\mathcal R_{10i}^2 + \mathcal R_{10q}^2},$$

the contributions of infectious and of quarantined humans. Let $\mathcal R_0$ denote the same quantity with $\sigma = 0$, so $\mathcal R_{10} \le \mathcal R_0$.

**Theorem 2.** The disease-free equilibrium is locally asymptotically stable if $\mathcal R_{10} < 1$, unstable if $\mathcal R_{10} > 1$, and globally asymptotically stable if $\mathcal R_0 \le 1$.

**Theorem 3 (backward bifurcation).** The model undergoes a backward bifurcation at $\mathcal R_{10} = 1$ if

$$ac\big(\theta\gamma_1(1-\sigma) + \gamma_2\big) + \mu\big(\theta\gamma_1(1 - 2\sigma) + \gamma_2\big) < 0,$$

which requires efficient quarantine ($\sigma > 1/2$). Then up to two endemic equilibria exist for $\mathcal R_{10} < 1$ (Proposition 1), and the disease can persist although $\mathcal R_{10} < 1$; the disease persists uniformly when $\mathcal R_{10} > 1$ (Theorem 4). With bilinear (mass-action) incidence the analogous number $\mathcal R_{20}$ gives forward threshold behavior with a unique endemic equilibrium (Theorems 5-6).

## Expansion

At the disease-free state the infected subsystem is linear with $F_1 = \begin{pmatrix} 0 & 0 & ab\\ 0&0&0\\ acm & (1-\sigma)acm & 0\end{pmatrix}$ and $V_1$ lower triangular, and the spectral radius of $F_1V_1^{-1}$ is the stated square root. For global stability, bound both incidence terms from above by their values with $\sigma = 0$ and full susceptible pools; the infected vector then satisfies $x' \le (F - V)x$, and the Lyapunov function $L = w V^{-1} x$, with $w$ a left Perron vector of $V^{-1}F$, satisfies $L' \le (\mathcal R_0 - 1)\, w x \le 0$. The gap between $\mathcal R_{10}$ and $\mathcal R_0$ is where the backward bifurcation lives: because quarantined people withdraw from the bite pool, bites concentrate on the remaining hosts as $Q_h$ grows (the denominator $H - \sigma Q_h$), a positive feedback that the center-manifold coefficient captures in the inequality of Theorem 3.

## Sources

- X. Jin, S. Jin, D. Gao, "Mathematical Analysis of the Ross-Macdonald Model with Quarantine", Bulletin of Mathematical Biology 82(4) (2020) 47, Equations (1)-(9), Proposition 1, Theorems 1-6, <https://doi.org/10.1007/s11538-020-00723-0>, PMCID PMC7117789.
