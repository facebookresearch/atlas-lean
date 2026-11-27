# Two-strain malaria model with treatment failure and bed nets

**Model.** Human proportions $s, i_r, i_s, \tau_r, \tau_s, r$ (susceptible; infected with resistant or sensitive strain; treated with resistant or sensitive strain; temporarily immune) sum to $1$, and mosquito proportions $x, y$ (susceptible, infected) sum to $1$. With $m$ female mosquitoes per human, biting-adjusted transmission rates $\beta$ (mosquito to human) and $\alpha_r, \alpha_s$ (human to mosquito), bed-net efficacy $c \in [0,1)$, resistant fraction of new infections $\rho \in [0,1]$, human and mosquito turnover $\mu, \xi$,

$$\begin{aligned}
\dot s &= \mu - \Lambda s y - \mu s + \omega r, & \dot \tau_r &= \sigma_r i_r - k_r \tau_r,\\
\dot i_r &= \rho \Lambda s y - b_r i_r + \epsilon_r \tau_r, & \dot \tau_s &= \sigma_s i_s - k_s \tau_s,\\
\dot i_s &= (1-\rho)\Lambda s y - b_s i_s + \epsilon_s \tau_s, & \dot r &= \gamma_r \tau_r + \gamma_s \tau_s - (\omega + \mu) r,\\
\dot x &= \xi - (a_r i_r + a_s i_s) x - \xi x, & \dot y &= (a_r i_r + a_s i_s) x - \xi y,
\end{aligned}$$

where $\Lambda = (1-c) m \beta$, $a_j = (1-c)\alpha_j$, $b_j = \sigma_j + \mu$, $k_j = \gamma_j + \epsilon_j + \mu$, $l_j = \gamma_j + \mu$ ($j \in \{r, s\}$), $\sigma_j$ is the treatment rate, $\gamma_j$ the recovery rate under treatment, $\epsilon_j$ the treatment-failure rate and $\omega$ the rate of waning immunity.

**Reproduction number.** The disease-free equilibrium is $(s, i_r, i_s, \tau_r, \tau_s, r, x, y) = (1,0,0,0,0,0,1,0)$. With infected variables $(i_r, i_s, \tau_r, \tau_s, y)$, the next-generation matrix $FV^{-1}$ has spectral radius $\sqrt{\mathcal{R}_0}$, where

$$\mathcal{R}_0 = \mathcal{R}_{0r} + \mathcal{R}_{0s}, \qquad \mathcal{R}_{0j} = \frac{\rho_j\, \Lambda\, a_j\, k_j}{\xi\,(\sigma_j l_j + \mu k_j)}, \quad \rho_r = \rho,\ \rho_s = 1-\rho,$$

explicitly $\mathcal{R}_{0j} = (1-c)^2 \rho_j m \beta \alpha_j (\epsilon_j + \gamma_j + \mu) / \{\xi[\sigma_j(\gamma_j + \mu) + \mu(\epsilon_j + \gamma_j + \mu)]\}$. Here $\mathcal{R}_0$ counts infections over a full human–mosquito–human cycle, so $\mathcal{R}_0 < 1$ iff $\rho(FV^{-1}) < 1$.

**Results.**

1. The disease-free equilibrium is globally asymptotically stable when $\mathcal{R}_0 < 1$ (proved for $\omega = 0$ via the [Castillo-Chavez–Feng–Huang criterion](../../part-01/global-stability-of-disease-free-equilibria/castillo-chavez-feng-huang-global-stability-criterion.md)).
2. Let $\omega = 0$. Every equilibrium with $y^* > 0$ has $i_j^* = \rho_j \Lambda s^* y^* k_j/(\sigma_j l_j + \mu k_j) = \xi \mathcal{R}_{0j} s^* y^*/a_j$ and $\tau_j^* = \sigma_j i_j^*/k_j$, so for $0 < \rho < 1$ both strains are present: the only endemic equilibrium is the coexistence one, which exists iff $\mathcal{R}_0 > 1$ and has $s^* = \dfrac{\mathcal{R}_0 \mu + \Lambda}{\mathcal{R}_0(\mu + \Lambda)}$ and $y^* = \mu(1 - s^*)/(\Lambda s^*)$. Single-strain endemic equilibria occur only for $\rho \in \{0, 1\}$, where only one strain is transmitted and $\mathcal{R}_0$ equals that strain's $\mathcal{R}_{0j}$. (For $\omega > 0$ the $s$-equation gives instead $y^* = (\mu(1 - s^*) + \omega r^*)/(\Lambda s^*)$.)
3. Bed nets act quadratically: $\mathcal{R}_0 \propto (1-c)^2$, since they reduce both mosquito-to-human and human-to-mosquito transmission.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Proof depends on

- [Castillo-Chavez–Feng–Huang global stability criterion](../../part-01/global-stability-of-disease-free-equilibria/castillo-chavez-feng-huang-global-stability-criterion.md)

## Expansion

The next-generation computation inverts $V$ blockwise: for each strain the $2 \times 2$ block $\begin{pmatrix} b_j & -\epsilon_j \\ -\sigma_j & k_j\end{pmatrix}$ has determinant $b_j k_j - \epsilon_j\sigma_j = \sigma_j l_j + \mu k_j$, the expected time spent infectious (untreated or failing treatment) per infection being $k_j/(\sigma_j l_j + \mu k_j)$. Treatment failure lengthens this time, which is why $\epsilon_j$ raises $\mathcal{R}_{0j}$. The rank-one vector-host structure of $F V^{-1}$ makes its nonzero eigenvalues $\pm\sqrt{\mathcal{R}_{0r} + \mathcal{R}_{0s}}$, so strain contributions add at the level of the two-generation number. The (H2) condition of the global criterion holds because the subtracted terms $\Lambda y (1 - s)$ and $a_j i_j (1 - x)$ are nonnegative when proportions are at most one.

## Sources

- O. C. Collins, K. J. Duffy, "A mathematical model for the dynamics and control of malaria in Nigeria", Infectious Disease Modelling 7 (2022) 728–741, Section 2 (models (1)–(2)), Section 3.1 (equations (3)–(8), Theorem 1) and Appendix 1, <https://doi.org/10.1016/j.idm.2022.10.005>.
