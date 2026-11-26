# Threshold dynamics of the multipatch SVEIR model with NPIs and vaccination

**Model.** In each of $n$ patches the population is split into susceptible $S_i$, vaccinated $V_i$, non-infectious exposed $E_{1i}$, infectious pre-symptomatic $E_{2i}$, infectious infected $I_{1i}$, a second, non-transmitting infected stage $I_{2i}$ and recovered $R_i$. With force of infection
$$\lambda_i = \beta_i\Big[(1-C_{ai})\frac{E_{2i}}{N_i} + (1-C_{si})\frac{I_{1i}}{N_i}\Big],$$
where $C_{ai}, C_{si} \in [0,1]$ are the intensities of non-pharmaceutical interventions (NPIs) against pre-symptomatic and symptomatic transmission,
$$\begin{aligned}
\dot S_i &= \Lambda_i - \lambda_iS_i - (\xi_i + \mu_i)S_i + \textstyle\sum_j A_{ij}S_j, &
\dot V_i &= \xi_iS_i - (1-\tau_i)\lambda_iV_i - \mu_iV_i + \textstyle\sum_j A_{ij}V_j,\\
\dot E_{1i} &= \lambda_i\big(S_i + (1-\tau_i)V_i\big) - \big(D_{E_{1i}}^{-1} + \mu_i\big)E_{1i} + \textstyle\sum_j B_{ij}E_{1j}, &
\dot E_{2i} &= D_{E_{1i}}^{-1}E_{1i} - \big(D_{E_{2i}}^{-1} + \mu_i + d_i\big)E_{2i} + \textstyle\sum_j C_{ij}E_{2j},
\end{aligned}$$
followed by $E_{2i} \to I_{1i} \to I_{2i} \to R_i$ with mean durations $D_{E_{2i}}, D_{I_{1i}}, D_{I_{2i}}$. Here $\xi_i$ is the vaccination rate, $\tau_i$ the vaccine efficacy (leaky vaccine), $\mu_i$ natural and $d_i$ disease mortality, and $A, B, C, D$ are migration matrices between patches. The paper's assumptions (A1)–(A2) concern these matrices; under them there is a disease-free equilibrium $\mathcal E^* = (S^*, V^*, 0,0,0,0,0)$.

**Theorem.** For every non-negative initial value there is a unique non-negative solution, and all solutions are uniformly and ultimately bounded. Let $Y$ be the new-infection Jacobian and $Z$ the transition-and-migration matrix of the infected subsystem at $\mathcal E^*$, and $\mathscr R_0 = \rho(YZ^{-1})$. Then:
1. $\mathscr R_0 - 1$ has the same sign as the spectral bound $s(Y - Z)$.
2. If $\mathscr R_0 < 1$, the disease-free equilibrium $\mathcal E^*$ is globally attractive.
3. If $\mathscr R_0 > 1$, the disease is uniformly persistent: there is $\tilde\varepsilon > 0$ such that every solution with some initial infection satisfies $\liminf_{t\to\infty}E_{1i}(t),\ \liminf E_{2i}(t),\ \liminf I_{1i}(t) > \tilde\varepsilon$ in every patch.

In a single patch the effective susceptible pool at $\mathcal E^*$ is $\frac{\Lambda}{\mu}\cdot\frac{\mu + \xi(1-\tau)}{\mu + \xi}$, and $\mathscr R_0$ is linear in $\beta$ times a weighted sum of $(1-C_a)$ and $(1-C_s)$: NPIs and vaccination lower $\mathscr R_0$ multiplicatively and additively in transparent ways, which the authors use to compare intervention scenarios fitted to Indian case data.

## Expansion

This is the van den Driessche–Watmough next-generation framework: with infected compartments $x = (E_1, E_2, I_1)$ (and $I_2$, which does not transmit), linearizing at $\mathcal E^*$ gives $\dot x = (Y - Z)x$, with $Y \ge 0$ and $Z$ a non-singular M-matrix, so $s(Y - Z) < 0 \iff \rho(YZ^{-1}) < 1$. Global attractivity below threshold follows by comparison: $S_i \le S_i^*$ and $V_i \le V_i^*$ asymptotically, so the infected subsystem is dominated by the linear cooperative system $\dot x = (Y - Z)x$, whose solutions decay. Uniform persistence above threshold uses the theory of persistence for dissipative systems (Zhao): the disease-free set is a uniform weak repeller because $s(Y - Z) > 0$, and migration spreads infection to all patches.

## Sources

- Bin-Guo Wang, Shunxiang Huang, Yongping Xiong and Ming-Zhen Xin, "Transmission Dynamics of COVID-19 Pandemic Non-pharmaceutical Interventions and Vaccination", arXiv:2107.02962 (2021), model equations, well-posedness and boundedness theorem, sign theorem for $\mathscr R_0 - 1$, global attractivity and uniform persistence theorems, <https://doi.org/10.48550/arXiv.2107.02962>.
