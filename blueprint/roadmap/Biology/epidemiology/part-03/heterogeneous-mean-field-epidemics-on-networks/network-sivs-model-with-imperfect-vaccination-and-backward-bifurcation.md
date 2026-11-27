# Network SIVS model with imperfect vaccination and backward bifurcation

**Model.** On an uncorrelated network with degree distribution $P(k)$, $k = 1, \dots, n$, and mean degree $\langle k\rangle$, let $S_k, I_k, V_k \ge 0$ with $S_k + I_k + V_k = 1$ be the susceptible, infected and vaccinated fractions of degree-$k$ nodes, and $\Theta = \langle k\rangle^{-1}\sum_k k P(k) I_k$. With degree-dependent transmission rates $0 < \beta_V(k) < \beta_S(k)$ for vaccinated and unvaccinated nodes, vaccination rates $\varphi_k \ge 0$, waning rate $\phi > 0$ and recovery rate $\gamma > 0$:

$$\begin{aligned}
S_k' &= \gamma I_k - \beta_S(k) S_k\Theta + \phi V_k - \varphi_k S_k, \\
I_k' &= \big[\beta_S(k) S_k + \beta_V(k) V_k\big]\Theta - \gamma I_k, \\
V_k' &= \varphi_k S_k - \beta_V(k) V_k\Theta - \phi V_k .
\end{aligned}$$

The disease-free equilibrium is $S_k^0 = \phi/(\varphi_k + \phi)$, $I_k^0 = 0$, $V_k^0 = \varphi_k/(\varphi_k + \phi)$.

**Theorem.** Define

$$R_0 = \frac{1}{\gamma\langle k\rangle}\sum_{k=1}^{n} \frac{k P(k)\big[\phi\beta_S(k) + \varphi_k \beta_V(k)\big]}{\varphi_k + \phi}, \qquad R_1(k) = \frac{\gamma\varphi_k\beta_V(k)\big[\beta_S(k) - \beta_V(k)\big]}{\big[\phi\beta_S(k) + \varphi_k\beta_V(k)\big]^2}.$$

1. The disease-free equilibrium is locally asymptotically stable if $R_0 < 1$.
2. If $R_1(k) \le 1$ for every $k$ and $R_0 > 1$, there is exactly one endemic equilibrium.
3. If $R_1(k) \le 1$ for every $k$, there is no endemic equilibrium when $R_0 \le 1$ (forward bifurcation at $R_0 = 1$).
4. If $R_1(k) > 1$ for some $k$, the model can have two endemic equilibria with $R_0 < 1$ (the source gives sufficient conditions for this in terms of further thresholds): imperfect vaccination produces a backward bifurcation, so reducing $R_0$ just below $1$ need not eradicate the infection.

Endemic equilibria are in bijection with roots $\Theta \in (0, 1)$ of $f(\Theta) = 0$, where

$$f(\Theta) = \frac{1}{\langle k\rangle}\sum_{k} \frac{k P(k)\big\{\beta_S(k)[\beta_V(k)\Theta + \phi] + \varphi_k\beta_V(k)\big\}}{[\beta_S(k)\Theta + \gamma][\beta_V(k)\Theta + \phi] + \varphi_k[\beta_V(k)\Theta + \gamma]} - 1, \qquad f(0) = R_0 - 1, \quad f(1) < 0 .$$

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

New infections at the disease-free state enter class $k$ at rate $[\beta_S(k) S_k^0 + \beta_V(k) V_k^0]\Theta$, a rank-one next-generation matrix, so $R_0$ is its trace. Solving the stationary equations for fixed $\Theta$ gives $S_k, I_k, V_k$ as rational functions of $\Theta$, and $\Theta = \langle k\rangle^{-1}\sum k P(k) I_k$ reduces to $\Theta f(\Theta) = 0$. The sign of $f'$ is that of $h_k(\Theta) = -[\beta_S\beta_V]^2\Theta^2 - 2\beta_S\beta_V[\phi\beta_S + \varphi_k\beta_V]\Theta + g_k$ summed with positive weights, where a direct computation gives $g_k = \gamma\varphi_k\beta_V(\beta_S - \beta_V) - [\phi\beta_S + \varphi_k\beta_V]^2$; thus $g_k \le 0$ iff $R_1(k) \le 1$. When every $g_k \le 0$, $f$ is decreasing on $(0, 1)$, giving items 2–3; when some $g_k > 0$, $f$ need not be monotone and can cross zero twice even though $f(0) < 0$ (with several degree classes it can even have three roots in $(0,1)$ when $R_0 > 1$, which is why item 2 needs $R_1(k) \le 1$). The mechanism is that vaccinated nodes become infectable at the reduced rate $\beta_V$ and, once infected, return to the fully susceptible class, which feeds the infection when prevalence is high. Setting $\beta_S(k) = \beta k$, $\beta_V(k) = \sigma\beta k$ and $\varphi_k = \varphi$ recovers the constant-rate network vaccination model the source generalizes.

## Sources

- W. Lv, Q. Ke, K. Li, "Dynamical analysis and control strategies of an SIVS epidemic model with imperfect vaccination on scale-free networks", *Nonlinear Dynamics* 99 (2020) 1507–1523, model (1), Section 3.1 (Eqs. (2)–(10), Theorem 1, Remark 4), Theorem 2 and Appendix A; the simplified form of $g_k$ is derived here. <https://doi.org/10.1007/s11071-019-05371-1> (PMC7089206).
