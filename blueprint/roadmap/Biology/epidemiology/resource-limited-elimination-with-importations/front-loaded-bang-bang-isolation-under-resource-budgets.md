# Front-loaded bang-bang isolation and traveller quarantine under resource budgets

**Model.** On a fixed horizon $[0,T]$ consider a community with susceptibles $S(t)$, infectious community members $I_1(t)$ and infectious arriving travellers who do not self-isolate $I_2(t)$, together with cumulative resource use $U_1(t)$ (test-trace-isolate) and $U_2(t)$ (traveller isolation):

$$
\begin{aligned}
\dot S &= -\beta S (I_1 + I_2), \\
\dot I_1 &= \beta S (I_1 + I_2) - (\mu + u_1) I_1, \\
\dot I_2 &= p\theta (1 - u_2) - \gamma I_2, \\
\dot U_1 &= u_1 I_1, \qquad \dot U_2 = \theta u_2,
\end{aligned}
$$

with $\beta,\mu,\theta>0$, $p\in(0,1)$, $\gamma>\mu$, $S(0),I_1(0),I_2(0)>0$ and $U_1(0)=U_2(0)=0$. The controls are piecewise continuous, $u_1:[0,T]\to[0,u_{1\max}]$ (isolation rate per infected community member) and $u_2:[0,T]\to[0,u_{2\max}]$ with $u_{2\max}\in(0,1)$ (probability that a traveller isolates), subject to the budget constraints $U_1(T)\le U_{1\max}$ and $U_2(T)\le U_{2\max}$. The objective is to minimise cumulative community infections

$$
J = \int_0^T \beta S (I_1 + I_2)\, dt .
$$

**Theorem.** An optimal control is front-loaded bang-bang with at most one switch in each channel: there exist $\tau_1,\tau_2\in[0,T]$ such that, up to sets of measure zero,

$$
u_i^*(t) = \begin{cases} u_{i\max}, & 0 \le t < \tau_i, \\ 0, & \tau_i < t \le T, \end{cases} \qquad i = 1,2 .
$$

The optimal problem is normal (the cost multiplier $\lambda_0$ is positive), so the switch times are determined by the state and costate equations. With $\Psi = \lambda_0 + \lambda_S - \lambda_{I_1}$ and the reduced switching functions $\varphi_1 = \lambda_{U_1}^* - \lambda_{I_1}$, $\varphi_2 = \lambda_{U_2}^* - p\lambda_{I_2}$ (where $\lambda_{U_i}^*\le 0$ are the constant budget multipliers), both $\varphi_1$ and $\varphi_2$ are strictly decreasing on $[0,T]$, and $u_i^* = u_{i\max}$ when $\varphi_i>0$, $u_i^*=0$ when $\varphi_i<0$.

So under fixed budgets it is never optimal to hold isolation or travel measures back and introduce them later. Both measures should start at full strength and either last the whole horizon (elimination or suppression) or stop once, when the budget's shadow price exceeds their marginal benefit.

## Expansion

The Hamiltonian is affine in $(u_1,u_2)$, so Pontryagin's maximum principle selects the extreme value of $u_i$ wherever $\varphi_i\ne 0$. Non-degeneracy: if $\lambda_0=0$, the transversality conditions $\lambda_S(T)=\lambda_{I_1}(T)=\lambda_{I_2}(T)=0$ force the costates to vanish identically. Then some channel is unused, and its strictly negative budget multiplier contradicts complementary slackness $\lambda_{U_i}(U_i(T)-U_{i\max})=0$. The key identity $\tfrac{d}{dt}(\beta S\Psi) = -\beta S\dot\lambda_{I_1}$ turns $\dot\varphi_1$ into the solution of a scalar linear equation $\ddot\varphi_1 = (\mu + u_{1\max}\mathbf{1}_{\{\varphi_1>0\}} - \beta S)\dot\varphi_1$. Its terminal value is $\dot\varphi_1(T) = -\beta S(T)<0$, so $\dot\varphi_1<0$ throughout. For the traveller channel, $\tfrac{d}{dt}(e^{-\gamma t}\dot\varphi_2) = -p\beta S\dot\varphi_1 e^{-\gamma t} > 0$ and $\dot\varphi_2(T) = -p\beta S(T)<0$ give $\dot\varphi_2<0$. A strictly decreasing switching function crosses zero at most once, from positive to negative. Whether the resulting strategy is elimination, mitigation or resurgence is then governed by the control reproduction number $R_0^C = \beta S(0)/(\mu + u_{1\max})$ and by the budgets.

## Sources

- George Adu-Boahen, Troy Day, Michael J. Plank, Amy Hurford, "Regional factors determine the feasibility of an elimination strategy", arXiv 2026: Section 2 (model, constraints, cost), Theorem 1, Lemma 1, Lemma 2, Proposition 1, Proposition 2. <https://doi.org/10.48550/arXiv.2608.08956>
