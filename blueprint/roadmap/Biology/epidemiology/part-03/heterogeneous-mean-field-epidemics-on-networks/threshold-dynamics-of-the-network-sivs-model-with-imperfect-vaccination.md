# Threshold dynamics of the network SIVS model with imperfect vaccination

**Setting.** The [network SIVS model with imperfect vaccination](network-sivs-model-with-imperfect-vaccination-and-backward-bifurcation.md) on the invariant set $\Omega = \{0 \le S_k, I_k, V_k \le 1\}$, with vaccinated reproduction number $R_0$ and quantities $R_1(k)$ as defined there, and the vaccination-free number

$$\tilde R_0 = \frac{1}{\gamma\langle k\rangle}\sum_{k=1}^{n} k\,\beta_S(k) P(k) \ \ge\ R_0 .$$

**Theorem.**

1. If $\tilde R_0 < 1$, the disease-free equilibrium is globally asymptotically stable in $\Omega$.
2. If $R_0 > 1$, the infection is uniformly persistent: there is $\xi > 0$, independent of the initial data, with $\liminf_{t\to\infty}\sum_k P(k) I_k(t) \ge \xi$ whenever $\sum_k P(k) I_k(0) > 0$.
3. If $R_0 > 1$ and $R_1(k) \le 1$ for every $k$, every solution with $\sum_k P(k)I_k(0) > 0$ converges to the unique endemic equilibrium.
4. If $R_0 < 1$ and $R_1(k) \le 1$ for every $k$, the disease-free equilibrium is globally asymptotically stable.

In the band $R_0 < 1 \le \tilde R_0$ with some $R_1(k) > 1$, the outcome can depend on the initial condition.

## Depends on

- [Network SIVS model with imperfect vaccination and backward bifurcation](network-sivs-model-with-imperfect-vaccination-and-backward-bifurcation.md)

## Expansion

For item 1, write $S_k = 1 - I_k - V_k$; then

$$\Theta' = \frac{1}{\langle k\rangle}\sum_k kP(k)\Big\{\big[\beta_S(k)(1 - I_k) - (\beta_S(k) - \beta_V(k))V_k\big]\Theta - \gamma I_k\Big\} \le \gamma(\tilde R_0 - 1)\Theta,$$

so $\Theta \to 0$ exponentially and every $I_k \to 0$; the linear equations $V_k' \approx \varphi_k(1 - V_k) - \phi V_k$ then force $V_k \to V_k^0$. Item 2 follows from abstract persistence theory: the boundary $\{I \equiv 0\}$ carries the linear system $S_k' = \phi V_k - \varphi_k S_k$, whose only limit point is the disease-free equilibrium, and that equilibrium repels interior orbits when $R_0 > 1$, because near it $\Theta' \ge \gamma(m_\delta - 1)\Theta$ with $m_\delta > 1$. Item 3 uses monotone iteration: persistence gives a positive lower bound on $\Theta$, and alternately bounding $I_k$ and $V_k$ above and below produces nested sequences of bounds that, when $f$ has a single root (guaranteed by $R_1(k) \le 1$), squeeze to the endemic values. Item 4 is the source's Remark 5, which rests on local stability for $R_0 < 1$ together with the absence of endemic equilibria when $R_1(k) \le 1$; the global statement additionally needs that no other invariant set attracts interior orbits, which the source does not argue separately.

## Sources

- W. Lv, Q. Ke, K. Li, "Dynamical analysis and control strategies of an SIVS epidemic model with imperfect vaccination on scale-free networks", *Nonlinear Dynamics* 99 (2020) 1507–1523, Sections 3.2–3.3 (Theorems 3–5, Remark 5) and Appendices B–D. <https://doi.org/10.1007/s11071-019-05371-1> (PMC7089206).
