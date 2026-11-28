# Final-size bound under information-driven vaccination with distributed recovery

Consider the age-independent reduction of an immuno-epidemiological model in which recovery and death happen at distributed times after infection, and the vaccinated proportion $\rho(t)$ grows according to an information index $m(t)=m(I(t))$:

$$
\begin{aligned}
\dot S&=-\beta S(1-\rho)I\ \ (=:-J(t)),\\
\dot I&=J(t)-\int_0^t r(t-\zeta)J(\zeta)\,d\zeta-\int_0^t d(t-\zeta)J(\zeta)\,d\zeta,\\
\dot R&=\int_0^t r(t-\zeta)J(\zeta)\,d\zeta,\qquad \dot D=\int_0^t d(t-\zeta)J(\zeta)\,d\zeta,\\
\dot\rho&=\mathcal P(m(t))(1-\rho).
\end{aligned}
$$

Here $r,d\ge0$ are the recovery and death kernels, with $\int_\zeta^{t_0}(r+d)(\xi-\zeta)\,d\xi\le1$ for all $\zeta<t_0$: the fraction of a cohort that has recovered or died by any time is at most $1$. Then $1-\rho(t)=(1-\rho_0)\exp\{-\int_0^t\mathcal P(m(I(\zeta)))\,d\zeta\}$, and the limit $S_f=\lim_{t\to\infty}S(t)$ satisfies

$$
S_0-S_f=\int_0^\infty J,\qquad \ln\frac{S_0}{S_f}=\beta\int_0^\infty(1-\rho(t))I(t)\,dt .
$$

Let $I_0=I(0)>0$ be the initial infectives (in this reduced system they are never resolved, since the recovery and death terms act only on the cohorts $J$). If the vaccination propensity is bounded below, $\mathcal P(m(I))\ge k>0$, then $\int_0^\infty(1-\rho)I\le\frac{1-\rho_0}{k}\big(I_0+\int_0^\infty J\big)$. Hence

$$
\ln\frac{S_0}{S_f}\le\frac{\beta(1-\rho_0)}{k}\big(I_0+S_0-S_f\big).
$$

With $x=S_f/S_0$, $\Lambda=\beta(1-\rho_0)S_0/k$ and $\iota=I_0/S_0$ this reads $h(x)\le0$, where $h(x)=-\ln x-\Lambda(1+\iota-x)$. The function $h$ is strictly convex on $(0,1]$ with $h(0^+)=+\infty$ and $h(1)=-\Lambda\iota<0$, so it has a unique zero $x^*\in(0,1)$, and $h>0$ on $(0,x^*)$, $h<0$ on $(x^*,1]$. So the surviving susceptible fraction satisfies $x\ge x^*$, and the attack ratio $1-S_f/S_0$ is at most $1-x^*$. Since $1+\iota-x>0$, $h$ increases pointwise as $\Lambda$ decreases; a higher minimal vaccination propensity $k$ lowers $\Lambda$, which raises $x^*$ and shrinks the bound on the epidemic. The bound never forces $S_f=S_0$ when $I_0>0$: the initial infectives alone give $\ln(S_0/S_f)\ge\beta I_0\int_0^\infty(1-\rho)>0$.

**Correction to the source.** The source's final-size estimate (final_size_F) in Section 4 of arXiv:2404.00365 bounds $\int(1-\rho)I$ by $\frac{1-\rho_0}{k}\int J$ alone, omitting the initial infectives $I_0$, and prints the resulting inequality as $\ln x/(x-1)\ge\Lambda$. Both are corrected here: the statement above keeps the $I_0$ term, and its inequality direction follows by substituting $x=S_f/S_0$ into the source's preceding display.

## Proof sketch

Write $I(t)=I_0+\int_0^tJ(\xi)\big[1-\int_\xi^t(r+d)(s-\xi)\,ds\big]d\xi$ by integrating the $I$ equation, multiply by $1-\rho$, and exchange the order of integration. The cohort condition puts the bracket in $[0,1]$, which gives $\int(1-\rho)I\le I_0\int_0^\infty(1-\rho)+\int J(\xi)\int_\xi^\infty(1-\rho)$. The exponential bound $1-\rho(t)\le(1-\rho_0)e^{-kt}$ then bounds both inner integrals by $(1-\rho_0)/k$. The full age-distributed model is well posed: a Banach fixed-point argument applies when $\mathcal P$ is Lipschitz.

## Sources

- Samiran Ghosh, Malay Banerjee and Vitaly Volpert, "An Age-Distributed Immuno-Epidemiological Model with Information-Based Vaccination Decision", *Mathematics* 14 (2025), 162, <https://doi.org/10.3390/math14010162>. Preprint version: arXiv:2404.00365 (2024), Section 3 (condition (cond), Theorem 2), Section 4 (reduced system (hpp11)–(hpp15) and final-size estimate (final_size_F)), <https://doi.org/10.48550/arXiv.2404.00365>.
