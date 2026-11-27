# Cycle-averaged growth of a phase-structured cell-cycle PDE

**PDE model.** Let $p(\phi,t)$ be the density of cells at cell-cycle position $\phi \in [0,1]$ ($\phi = 0$ the start of G1, $\phi = 1$ the end of M), with progression speed $v(\phi) > 0$ and no death:

$$\partial_t p + \partial_\phi\big(v(\phi)p\big) = 0, \qquad v(0)p(0,t) = 2v(1)p(1,t), \qquad p(\phi,0) = p_0(\phi).$$

Every cell divides exactly $\eta_1 = \int_0^1 d\phi/v(\phi)$ time units after its birth. Take $v = v_1$ on $[0,\tfrac12]$ (G1) and $v = u$ on $(\tfrac12,1]$ (S/G2/M), so the phase durations are $L_1 = 1/(2v_1)$ and $L_2 = 1/(2u)$ and $\eta_1 = L_1 + L_2$, with piecewise-constant initial data $p_0 = p_0^{(1)}$ on G1 and $p_0^{(2)}$ on the second phase.

**Proposition.**
1. The method of characteristics gives $p(\phi,t)$ explicitly; at each time it is piecewise constant with four pieces, and with $k(t) = \lfloor t/\eta_1\rfloor$ and $\tau = t - k(t)\eta_1$ it has the form $p(\phi,t) = 2^{k(t)}\,\tilde p(\phi,\tau)$.
2. Consequently the total population satisfies $N(t+\eta_1) = 2N(t)$, and the phase proportions $\pi_i(t) = \int_{\text{phase } i}p\,d\phi \,/\, N(t)$ are periodic with period $\eta_1$ for any initial phase distribution; they do not converge to a steady state.
3. The cycle-averaged exponential growth rate is

$$\bar\beta = \frac{\ln 2}{\eta_1} = \frac{2uv_1\ln 2}{u + v_1}.$$

**Comparison ODE.** The two-compartment model $\dot G_1 = -k_1G_1 + 2k_2G_2$, $\dot G_2 = k_1G_1 - k_2G_2$ grows at the dominant eigenvalue

$$\lambda_+ = \frac{-(k_1+k_2) + \sqrt{k_1^2 + 6k_1k_2 + k_2^2}}{2},$$

with phase-2 proportion converging to $\tilde g_2 = \lambda_+/k_2$ independently of initial conditions. Matching $\lambda_+ = \bar\beta$ and $\tilde g_2$ to the cycle-averaged PDE proportion $\bar\pi_2$ defines a corresponding ODE; since $\bar\pi_2$ depends on the initial phase ratio while $\bar\beta$ does not, two different initial ratios can map to the same ODE parameters, so the ODE cannot distinguish them.

## Expansion

Along characteristics $d\phi/dt = v(\phi)$ the flux $vp$ is conserved, so density jumps by $v_1/u$ or $u/v_1$ when a cohort crosses $\phi = 1/2$ and doubles when it passes through mitosis. After one full cycle every cohort has divided exactly once, giving the factor 2 and the time-periodic shape $\tilde p$, from which $N(t+\eta_1) = 2N(t)$ and periodicity of the proportions follow (for any speed profile $v(\phi)$, not only piecewise-constant ones). This persistent oscillation reflects the deterministic inter-mitotic time; in the ODE, exponentially distributed phase durations dephase cohorts and produce asynchronous exponential growth with fixed proportions. The ODE growth rate is the positive root of the characteristic polynomial $\lambda^2 + (k_1+k_2)\lambda - k_1k_2$ of its rate matrix, and $\tilde g_2$ follows from the eigenvector.

## Sources

- R. E. Nixson, H. M. Byrne, J. M. Pitt-Francis, P. K. Maini, "Characterising the behaviour of a structured PDE model of the cell cycle in contrast to a corresponding ODE system", Bulletin of Mathematical Biology (2025), Eqs. (1)–(27), (39)–(47) and Theorem 1, <https://doi.org/10.1007/s11538-025-01472-8>, PMCID PMC12146229.
