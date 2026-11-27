# Entry–exit delay in the Poletti imitation-dynamics model

**Model.** Let $S, I$ be the susceptible and infective fractions and $x \in [0,1]$ the fraction of susceptibles using normal behavior. Normal behavior has transmission rate $\beta_n$ with $\beta_n/\gamma > 1$; altered behavior (distancing, masks) has $\beta_a < \beta_n$ with $\beta_a/\gamma < 1$. Payoffs are $p_n = -m_n I$ and $p_a = -k - m_a I$ with $m_n > m_a > 0$, $k > 0$, so altered behavior pays more exactly when $I > I_c := k/(m_n - m_a)$, assumed $< 1$. With imitation dynamics on a fast time scale $\rho = 1/\epsilon$:

$$\dot S = -(\beta_n x + \beta_a(1-x)) S I, \quad \dot I = (\beta_n x + \beta_a(1-x)) S I - \gamma I,$$

$$\epsilon \dot x = \epsilon\, x(1-x)(\beta_a - \beta_n) I + x(1-x)\big(k - (m_n - m_a) I\big).$$

**Slow–fast structure.** In the limit $\epsilon = 0$, the planes $x = 0$ and $x = 1$ are critical manifolds carrying SIR flows with $\beta = \beta_a$ and $\beta = \beta_n$ respectively. The sheet $x = 1$ is normally attracting for $I < I_c$ and repelling for $I > I_c$; $x = 0$ is the reverse.

**Entry–exit function.** For a slow SIR orbit $(S(t), I(t))$ on the sheet $x = 0$ entering at $(S_0, I_0)$ with $I_0 > I_c$, define

$$\mathcal{I}_0\big((S_0,I_0),(S_1,I_1)\big) = \int_0^{t_1} \big(k - (m_n - m_a) I(t)\big)\,dt = \int_{S_0}^{S_1} \frac{k - (m_n - m_a)\,I(S)}{-\beta_a S\, I(S)}\,dS,$$

with $I(S) = v_0 - S + (\gamma/\beta_a)\ln S$ the SIR orbit through $(S_0, I_0)$. There is exactly one $t_1 > 0$ with $\mathcal{I}_0 = 0$, and the exit point $(S_1, I_1)$ satisfies $I_1 < I_c$; the analogous integral $\mathcal{I}_1$ with $\beta_n$ governs exit from $x = 1$, which may fail to vanish, in which case the orbit stays on $x = 1$ until the epidemic ends.

**Theorem.** Let $(S_0, I_0) \in \{S > 0, I > 0, S + I \le 1\}$, $I_0 \ne I_c$, $0 < x_0 < 1$. Build the singular orbit by alternating fast vertical jumps in $x$ with slow SIR arcs on $x = 0$ and $x = 1$, leaving each sheet at the point where the entry–exit integral returns to $0$. If this construction never hits the degenerate case $I_1 = I_c$ and ends after finitely many steps at $(S_f, 0, 1)$, then as $\epsilon \to 0$ the orbit of the full system from $(S_0, I_0, x_0)$ converges to the singular orbit, and its final susceptible fraction converges to $S_f$.

## Expansion

Along a sheet, $\log x$ (or $\log(1-x)$) evolves at the rate $(k - (m_n - m_a)I)/\epsilon$ to leading order, so a trajectory that has been attracted toward $x = 0$ while $I > I_c$ must spend an equal accumulated amount of repulsion after $I$ drops below $I_c$ before it can leave. This is the entry–exit (way-in/way-out) principle of geometric singular perturbation theory, which also requires tracking the $O(\epsilon)$ term $x(1-x)(\beta_a - \beta_n)I$. The resulting delay makes behavior "sticky": with $\mathcal{R}_0 = 3$ under normal behavior, $0.6$ under altered behavior and $I_c = 0.1$, the population switches to altered behavior only near $I \approx 0.18$ and back near $I \approx 0.05$, producing second and later waves before the epidemic ends.

## Sources

- S. Schecter, "Geometric singular perturbation theory analysis of an epidemic model with spontaneous human behavioral change", Journal of Mathematical Biology (2021), model (7)–(12), Sections 4–5 (fast and slow limit systems, entry–exit integral (27), Proposition 1) and Theorem 1, <https://doi.org/10.1007/s00285-021-01605-2>, PMCID PMC8092374.
