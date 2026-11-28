# Zero-sum vaccination game on a hesitancy-structured SIR system

**Setting.** Susceptibles are structured by their leaning toward vaccination $\xi \in [0,1]$ ($\xi = 0$: never vaccinates, $\xi = 1$: certainly vaccinates), with density $S(t,\xi)$; $I(t)$ is the density of infected individuals. Two players act through controls $u_1(t) \in [0,M_1]$ (public-health authority promoting vaccination) and $u_2(t) \in [0,M_2]$ (anti-vaccination campaigning). The state evolves by the coupled PDE–ODE system

$$\partial_t S + \partial_\xi\big(g(\xi,u_1,u_2)\,S\big) = -\big(f(\xi) + \alpha(I)\big)S, \qquad \dot I = -\beta I + \alpha(I)\int_0^1 S(t,\xi)\,d\xi,$$

where $\alpha$ is Lipschitz with $\alpha(0) = 0$ (force of infection), $\beta > 0$ is the removal rate, $f$ is Lipschitz, non-decreasing, $f(0) = 0$, $f(1) = 1$ (vaccination rate by leaning), and the opinion flux $g$ is continuous, $C^2$ in $\xi$, vanishes at $\xi = 0, 1$ and has $|\partial_\xi g| \le \gamma$. The discounted cost, minimized by player 1 and maximized by player 2 ($\mathcal{F}_1 + \mathcal{F}_2 = 0$), is

$$\mathcal{F}(S_o,I_o,u_1,u_2) = \int_0^\infty e^{-\theta t}\Big(\kappa\big(I(t) + u_1(t)\big) - u_2(t) - \int_0^1 g(\xi,u_1(t),u_2(t))\,d\xi\Big)\,dt.$$

**Theorem (state system).** For fixed controls and $S_o \in L^2((0,1);\mathbb{R}^+)$, $I_o \ge 0$, there is a unique global solution, with

$$\|S(t)\|_{L^1} \le \|S_o\|_{L^1}, \qquad \|S(t)\|_{L^2} \le e^{\gamma t/2}\|S_o\|_{L^2}, \qquad I(t) \le \|S_o\|_{L^1} + I_o,$$

$H^1$ regularity propagates, and solutions depend Lipschitz-continuously (in $L^1 \times \mathbb{R}$, with time-dependent constants) on the initial data. For each fixed control of one player, the other player's optimization problem has a solution.

**Theorem (game values).** Let $V$ (lower value: inf over player 1's non-anticipating strategies of sup over $u_2$) and $U$ (upper value: sup over player 2's non-anticipating strategies of inf over $u_1$) be the values. Both satisfy a dynamic programming principle, and $V$, resp. $U$, is a viscosity solution of the infinite-dimensional Hamilton–Jacobi–Isaacs equation

$$\theta W + \mathcal{H}(Y,\nabla W) = 0, \qquad Y = (S,I) \in H^1((0,1)) \times \mathbb{R},$$

with the lower Hamiltonian $\underline{\mathcal{H}}$, resp. upper Hamiltonian $\overline{\mathcal{H}}$, defined for $Y=(S,I)\in H^1((0,1))\times\mathbb R$ and $P=(p,q)\in L^2((0,1))\times\mathbb R$ from the pre-Hamiltonian

$$\mathcal H(Y,P,u_1,u_2)=\Big\langle \partial_\xi(gS)+\big(f+\alpha(I)\big)S,\ p\Big\rangle_{L^2}+\Big(\beta I-\alpha(I)\int_0^1S(\xi)\,d\xi\Big)q-\ell(I,u_1,u_2),\qquad \ell(I,u_1,u_2)=\kappa(I+u_1)-u_2-\int_0^1g(\xi,u_1,u_2)\,d\xi,$$

by

$$\underline{\mathcal H}(Y,P)=\min_{u_2\in[0,M_2]}\ \max_{u_1\in[0,M_1]}\mathcal H(Y,P,u_1,u_2),\qquad \overline{\mathcal H}(Y,P)=\max_{u_1\in[0,M_1]}\ \min_{u_2\in[0,M_2]}\mathcal H(Y,P,u_1,u_2)$$

(the source's (2.22)–(2.24)). Note the sign convention: $\mathcal H$ is minus the pairing of $P$ with the dynamics, minus the running cost.

## Expansion

The PDE is a linear transport equation in the leaning variable with a non-local coupling to the ODE through $\int S$; since $g$ vanishes at the endpoints, no boundary data are needed, and the method of characteristics plus a fixed point on $I$ gives existence and the $L^1$ and $L^2$ bounds (the latter growing with the compressibility bound $\gamma$). Non-anticipating strategies (Elliott–Kalton) let each player react to the other's past controls; the dynamic programming principle follows from the semigroup property and continuous dependence, and the viscosity property follows by testing with $C^1$ functions in $L^2 \times \mathbb{R}$, the subtlety being that $\partial_\xi(gS)$ is only defined for $S \in H^1$, which dictates the state space of the Hamilton–Jacobi–Isaacs equation.

## Sources

- Mauro Garavello, Elena Rossi and Abraham Sylla, "Differential Games for a Mixed ODE-PDE System", arXiv:2412.12712 (2024), hypotheses (alpha), (F), (G), Theorems 2.3, 2.4, 2.5, 2.9 and 2.11, equations (2.22)–(2.24), <https://doi.org/10.48550/arXiv.2412.12712>. Published version: SIAM Journal on Control and Optimization 63 (2025) 3557–3587, <https://doi.org/10.1137/24m1699760>.
