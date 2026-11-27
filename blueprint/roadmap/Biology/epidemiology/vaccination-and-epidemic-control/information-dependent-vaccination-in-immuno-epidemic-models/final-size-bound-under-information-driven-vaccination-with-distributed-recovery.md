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

If the vaccination propensity is bounded below, $\mathcal P(m(I))\ge k>0$, then $\int_0^\infty(1-\rho)I\le\frac{1-\rho_0}{k}\int_0^\infty J$. Hence

$$
\frac{\ln(S_0/S_f)}{S_0-S_f}\le\frac{\beta(1-\rho_0)}{k}.
$$

With $x=S_f/S_0$ and $\Lambda=\beta(1-\rho_0)S_0/k$ this reads $\frac{\ln x}{x-1}\le\Lambda$. The function $G(x)=\ln x/(x-1)$ decreases strictly on $(0,1)$ from $+\infty$ to $1$. So if $\Lambda>1$, the surviving susceptible fraction satisfies $x\ge x^*$, where $x^*\in(0,1)$ solves $G(x^*)=\Lambda$, and the attack ratio is at most $1-x^*$. If $\Lambda\le1$, then $G(x)>1\ge\Lambda$ for every $x\in(0,1)$, which forces $S_f=S_0$: no epidemic. A higher minimal vaccination propensity $k$ lowers $\Lambda$, which raises $x^*$ and shrinks the bound on the epidemic.

## Proof sketch

Write $I$ as the infections that have not yet been resolved, multiply by $1-\rho$, and exchange the order of integration. The cohort condition makes the resolved fraction at most one, which gives $\int(1-\rho)I\le\int J(\xi)\int_\xi^\infty(1-\rho)$. The exponential bound on $1-\rho$ then gives the factor $1/k$. The source prints the final inequality as $\ln x/(x-1)\ge\Lambda$. Substituting $x=S_f/S_0$ into its preceding display gives the direction stated here. The full age-distributed model is well posed: a Banach fixed-point argument applies when $\mathcal P$ is Lipschitz.

## Sources

- Samiran Ghosh, Malay Banerjee and Vitaly Volpert, "An Age-Distributed Immuno-Epidemiological Model with Information-Based Vaccination Decision", *Mathematics* 14 (2025), 162, <https://doi.org/10.3390/math14010162>. Preprint version: arXiv:2404.00365 (2024), Section 3 (condition (cond), Theorem 2), Section 4 (reduced system (hpp11)–(hpp15) and final-size estimate (final_size_F)), <https://doi.org/10.48550/arXiv.2404.00365>.
