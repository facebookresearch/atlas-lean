# Threshold disconnection policy for individual safety in networked SIR epidemics

**Model.** On a contact graph with node set $\mathcal V$ and neighborhoods $\mathcal N_i$, each node $i$ is in state $X_i(t)\in\{S,I,R\}$ of a continuous-time Markov SIR process: a susceptible node is infected by each infected neighbor $j$ at rate $\beta$, and an infected node recovers at rate $\delta$. Node $i$ can cut its link to neighbor $j$ at time $t$ by setting $u_{ij}(t)\in[0,1]$ at cost $c_{ij}$ per unit time; the link is active with weight $1-\max(u_{ij},u_{ji})$. The *individual safety problem* for node $1$ is

$$\min_{u_{1j}}\int_0^T\sum_{j\in\mathcal N_1}c_{1j}u_{1j}(t)\,dt\quad\text{s.t.}\quad \Pr[X_1(t)=S]\ge\tau_1\ \ \forall t\in[0,T],$$

where the exact marginal probabilities evolve by the $3^N$-state Kolmogorov equation.

**Mean-field relaxation (NIMFA).** With $\tilde x_i^S,\tilde x_i^I$ approximating $\Pr[X_i=S],\Pr[X_i=I]$,

$$\dot{\tilde x}_i^S=-\tilde x_i^S\sum_{j\in\mathcal N_i}\beta\bigl(1-\max(u_{ij},u_{ji})\bigr)\tilde x_j^I,\qquad \dot{\tilde x}_i^I=-\delta\tilde x_i^I+\tilde x_i^S\sum_{j\in\mathcal N_i}\beta\bigl(1-\max(u_{ij},u_{ji})\bigr)\tilde x_j^I .$$

**Theorem.**

1. *(Conservative relaxation.)* For every control, $\Pr[X_1(t)=S]\ge\tilde x_1^S(t)$ for all $t\in[0,T]$, so any control meeting $\tilde x_1^S\ge\tau_1$ is feasible for the exact stochastic problem.
2. *(Bang-bang structure.)* The optimal control of the relaxed problem is bang-bang: $u_{1j}=1$ when the switching function $c_{1j}+\sum_i(\lambda_{x_i^S}-\lambda_{x_i^I})\tilde x_i^S\tilde x_j^I$ is negative and $u_{1j}=0$ when it is positive, with $\lambda$ the Pontryagin costates.
3. *(Threshold form.)* If infection from node $1$ onward is ignored (it is irrelevant once node $1$ is infected), the relaxed problem is solved by cutting the link to neighbor $j$ exactly while that neighbor's infection probability exceeds a threshold,

$$u_{1j}(t)=\begin{cases}1,&\tilde x_j^I(t)>\mathcal T_j^I,\\0,&\tilde x_j^I(t)<\mathcal T_j^I,\end{cases}\qquad \mathcal T_j^I=\frac{-c_{1j}}{\beta\,\tau_1\,v}>0 ,$$

for a scalar multiplier $v<0$ of the safety constraint; for a well-mixed population lumped into one neighbor, a single threshold $I^*=-c_{\rm av}/(\beta\tau_1v)$ on the lumped infection probability gives the optimal connect/disconnect rule.

The thresholds exist but are not available in closed form; they are tuned numerically (e.g. by Monte Carlo on the exact process), giving a simple decentralized policy that each agent can run from local information.

## Expansion

The mean-field closure treats neighbor states as independent; for SIR dynamics positive correlations between neighbors make the true infection pressure on a susceptible node no larger than the mean-field one, which yields the inequality in item 1. The relaxed problem is control-affine with a linear running cost, so the Hamiltonian is minimized at an endpoint of $[0,1]$ wherever the switching function is nonzero. Restricting to inflow toward node $1$ decouples the costates, and the state constraint $\tilde x_1^S\ge\tau_1$ contributes a multiplier $v$; the switching function then changes sign exactly when $\beta\tau_1v\,\tilde x_j^I+c_{1j}$ does, which is the threshold rule.

## Sources

- M. Mubarak, C. Nowzari, "An Agent-Based Distributed Control of Networked SIR Epidemics", arXiv:2209.06250 (2022), Section II (problem formulations), Section III (continuous-time mean-field approximation and the relation theorem between exact and relaxed models) and Section IV (bang-bang solution form, threshold-solution theorem and the lumped-node theorem). <https://doi.org/10.48550/arXiv.2209.06250>
