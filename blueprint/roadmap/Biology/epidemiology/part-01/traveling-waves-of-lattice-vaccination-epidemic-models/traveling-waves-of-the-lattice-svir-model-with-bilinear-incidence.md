# Traveling waves of the lattice SVIR model with bilinear incidence

**Model.** On the patches $n \in \mathbb{Z}$ let $S_n, V_n, I_n, R_n$ be susceptible, vaccinated, infectious and removed densities, with

$$
\begin{aligned}
\frac{dS_n}{dt} &= [S_{n+1} - 2S_n + S_{n-1}] + \Lambda - \beta_1S_nI_n - \alpha S_n - \mu S_n, \\
\frac{dV_n}{dt} &= [V_{n+1} - 2V_n + V_{n-1}] + \alpha S_n - \beta_2V_nI_n - \gamma_1V_n - \mu V_n, \\
\frac{dI_n}{dt} &= d[I_{n+1} - 2I_n + I_{n-1}] + \beta_1S_nI_n + \beta_2V_nI_n - \gamma I_n - \mu I_n,
\end{aligned}
$$

and a decoupled equation for $R_n$. Here $\Lambda$ is recruitment, $\alpha$ the vaccination rate, $\gamma_1$ the rate at which vaccinees become fully immune, $\beta_1$ and $\beta_2$ the transmission rates to susceptibles and to vaccinees, $\gamma$ recovery, $\mu$ death, and $d > 0$ the motility of infectives relative to the normalised motility $1$ of the other classes. Set $\mu_1 = \alpha + \mu$, $\mu_2 = \gamma_1 + \mu$ and $\mu_3 = \gamma + \mu$. The spatially homogeneous system has the disease-free equilibrium $E_0 = (S_0, V_0, 0) = \left(\frac{\Lambda}{\mu_1}, \frac{\Lambda\alpha}{\mu_1\mu_2}, 0\right)$ and

$$
\mathcal{R}_0 = \frac{\beta_1S_0 + \beta_2V_0}{\mu_3}.
$$

For the ODE system, $E_0$ is globally asymptotically stable if $\mathcal{R}_0 < 1$, and if $\mathcal{R}_0 > 1$ there is a globally asymptotically stable endemic equilibrium $E^* = (S^*, V^*, I^*)$.

**Wave speed.** A traveling wave is a solution $(S_n, V_n, I_n)(t) = (S, V, I)(n + ct)$ with profile variable $\varsigma = n + ct$ and wave speed $c > 0$. Linearising the $I$ profile equation at $E_0$ and trying $I = e^{r\varsigma}$ gives the characteristic function

$$
\Delta(r, c) = d\left(e^{r} + e^{-r} - 2\right) - cr + \beta_1S_0 + \beta_2V_0 - \mu_3.
$$

If $\mathcal{R}_0 > 1$ there are $c^* > 0$ and $r^* > 0$ with $\Delta(r^*, c^*) = 0$ and $\partial_r\Delta(r^*, c^*) = 0$. Then $\Delta(\cdot, c) > 0$ for $0 < c < c^*$, $\Delta(\cdot, c^*)$ has the single positive root $r^*$, and for $c > c^*$, $\Delta(\cdot, c)$ has two positive roots $r_1 < r^* < r_2$.

**Theorem.** If $\mathcal{R}_0 > 1$, then for every $c > c^*$ the lattice system has a traveling wave $(S, V, I)(\varsigma)$ with

$$
\lim_{\varsigma\to-\infty}(S, V, I)(\varsigma) = (S_0, V_0, 0), \qquad \lim_{\varsigma\to+\infty}(S, V, I)(\varsigma) = (S^*, V^*, I^*),
$$

and $0 < S < S_0$, $0 < V < V_0$, $0 < I$ is bounded with $\liminf_{\varsigma\to+\infty}I(\varsigma) > 0$. The critical speed $c = c^*$ can be reached by a limiting argument.

The critical speed increases with the infective motility $d$ and with $\beta_1$, $\beta_2$, and decreases with the vaccine-completion rate $\gamma_1$. A more effective vaccine slows the invasion front as well as lowering $\mathcal{R}_0$.

## Expansion

Since $\Delta$ is strictly convex in $r$, equals $\mu_3(\mathcal{R}_0 - 1) > 0$ at $r = 0$, has slope $-c$ there and decreases in $c$, the tangency point $(r^*, c^*)$ exists and separates the speeds. For $c > c^*$, the functions $S^+ = S_0$, $V^+ = V_0$, $I^+ = e^{r_1\varsigma}$ and $S^- = \max\{S_0(1 - M_1e^{\varepsilon_1\varsigma}), 0\}$, $V^-$, $I^- = \max\{e^{r_1\varsigma}(1 - M_3e^{\varepsilon_3\varsigma}), 0\}$ are super- and sub-solutions of the wave-profile equations. A Schauder fixed-point argument on truncated intervals $[-B, B]$, followed by $B \to \infty$ with uniform $C^{1,1}$ bounds, produces a profile trapped between them, which gives the behaviour at $-\infty$. Boundedness of $I$ and persistence $\liminf I > 0$ at $+\infty$ are shown directly. Convergence to $E^*$ at $+\infty$ uses a Lyapunov functional made of $cS^*g(S/S^*) + cV^*g(V/V^*) + cI^*g(I/I^*)$, with $g(x) = x - 1 - \log x$, plus nonlocal terms $\int_0^1 g(\cdot(\varsigma-\sigma))\,d\sigma - \int_{-1}^0 g(\cdot(\varsigma-\sigma))\,d\sigma$ that absorb the discrete diffusion. The functional is nonincreasing along the profile and bounded below thanks to persistence.

## Sources

- Ran Zhang and Shengqiang Liu, "Wave propagation for a discrete diffusive vaccination epidemic model with bilinear incidence", arXiv:2203.08369 (2022), Section 2 (Theorem 2.1, Lemma 2.1 on the wave speed, Lemma 2.2 on sub- and super-solutions), Section 3 (Lemmas 3.1–3.2), Section 4 (Lemmas 4.1–4.3), Section 5 (Theorem 5.1 and Remark 5.1), Section 6 (parameter dependence of the wave speed), <https://doi.org/10.48550/arXiv.2203.08369>. Published version: Journal of Applied Analysis & Computation 13(2) (2023), 715–733, <https://doi.org/10.11948/20220040>; locators above refer to the arXiv version.
