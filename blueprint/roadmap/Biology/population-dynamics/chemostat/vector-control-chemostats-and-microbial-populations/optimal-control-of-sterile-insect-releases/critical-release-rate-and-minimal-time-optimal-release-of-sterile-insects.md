# Critical release rate and minimal-time optimal release of sterile insects

**Model.** Let $M$ and $F$ be wild males and fertilized wild females, and $M_S$ released sterile males, released at rate $u(t) \ge 0$:

$$
\begin{aligned}
\dot M &= r\rho\,\frac{F M}{M + \gamma M_S}\,e^{-\beta(M + F)} - \mu_M M,\\
\dot F &= (1 - r)\rho\,\frac{F M}{M + \gamma M_S}\,e^{-\beta(M + F)} - \mu_F F,\\
\dot M_S &= u(t) - \mu_S M_S ,
\end{aligned}
$$

with sex ratio $r \in (0,1)$, fecundity $\rho$, mating competitiveness $\gamma > 0$ of sterile males (a female mates with a wild male with probability $M/(M + \gamma M_S)$), density-dependent larval survival $e^{-\beta(M+F)}$ and mortalities $\mu_M, \mu_F, \mu_S$. The **basic offspring numbers** are

$$
\mathcal{N}_F = \frac{(1 - r)\rho}{\mu_F}, \qquad \mathcal{N}_M = \frac{r\rho}{\mu_M},
$$

and the wild population is naturally persistent when they exceed $1$. Solutions with bounded measurable $u \in [0, u_{\max}]$ exist, are unique, non-negative and remain in a bounded box.

**Theorem (critical constant release).** For constant release $u \equiv \Lambda$, $M_S \to \Lambda/\mu_S$, and the reduced $(M, F)$ system with $M_S = \Lambda/\mu_S$ is considered. Assume $\mathcal{N}_F > 1$, and let $\phi^{\mathrm{crit}} > 0$ be the unique positive solution of

$$
1 + \phi\Big(1 + \sqrt{1 + \tfrac{2}{\phi}}\Big) = \mathcal{N}_F \exp\Big[-\frac{2}{1 + \sqrt{1 + 2/\phi}}\Big], \qquad \Lambda^{\mathrm{crit}} = \frac{2\mu_S}{\beta\gamma}\,\frac{\phi^{\mathrm{crit}}}{1 + \mathcal{N}_F/\mathcal{N}_M} .
$$

The reduced system has two positive equilibria if $0 < \Lambda < \Lambda^{\mathrm{crit}}$, one if $\Lambda = \Lambda^{\mathrm{crit}}$ and none if $\Lambda > \Lambda^{\mathrm{crit}}$; in the last case the insect-free equilibrium $(0,0)$ is globally exponentially stable.

**Theorem (existence of an optimal release program).** Assume $\mathcal{N}_F > 1$ and $u_{\max} > \Lambda^{\mathrm{crit}}$. For weights $A_1, \dots, A_4 \ge 0$ and a small target $\varepsilon > 0$, the free-terminal-time problem

$$
\min_{0 \le u(t) \le u_{\max},\ 0 < T < \infty} \mathcal{J}(u, T) = A_1\big(F(T) - \varepsilon\big)^2 + \int_0^T \Big(A_2 F(t) + A_3 + \tfrac12 A_4 u(t)^2\Big)\,\mathrm{d}t
$$

has a solution $(u^*, T^*)$. By the maximum principle for free terminal time, the optimal control is the projection

$$
u^*(t) = \max\Big\{0, \min\Big\{\frac{\lambda_3(t)}{A_4},\ u_{\max}\Big\}\Big\},
$$

where $\lambda_3$ is the adjoint variable of $M_S$ in the paper's (maximized) Hamiltonian, and the Hamiltonian vanishes at $T^*$.

## Expansion

At an equilibrium of the reduced system, writing the female-to-male ratio and eliminating $F$ reduces the problem to the intersection of a monotone curve with an exponential, parametrized by $\phi$; the two branches merge in a saddle-node at $\Lambda^{\mathrm{crit}}$. Above the critical release rate no positive equilibrium remains and a Lyapunov or comparison argument gives global exponential convergence to elimination. Below it, the upper equilibrium is stable and constant releases fail. For the optimal control problem, existence follows from Filippov-Cesari type arguments: the state stays bounded, the control set is compact and convex, the dynamics are affine in $u$ and the running cost is convex in $u$. Since $u_{\max} > \Lambda^{\mathrm{crit}}$, the constant control $u_{\max}$ drives $F$ below $\varepsilon$ in finite time, so admissible pairs with finite cost exist. The quadratic cost makes $H_{uu} = -A_4 < 0$, which gives the projected formula for $u^*$. The $A_3$ term penalizes campaign duration, pushing towards releases near $u_{\max}$ early, which motivates periodic impulsive release schedules that approximate the continuous program.

## Sources

- Pierre-Alexandre Bliman, Daiver Cardona-Salgado, Yves Dumont and Olga Vasilieva, "Optimal Control Approach for Implementation of Sterile Insect Techniques", arXiv (2019), Section 2 (model, basic offspring numbers, Theorems 1 and 2 recalled from Bliman et al. 2019), Section 3 (optimal control problem, Theorem 3, maximum principle and the optimal control formula), <https://doi.org/10.48550/arXiv.1911.00034>.
- P.-A. Bliman, D. Cardona-Salgado, Y. Dumont and O. Vasilieva, "Implementation of control strategies for sterile insect techniques", Mathematical Biosciences 314 (2019), 43–60, <https://doi.org/10.1016/j.mbs.2019.06.002>.
