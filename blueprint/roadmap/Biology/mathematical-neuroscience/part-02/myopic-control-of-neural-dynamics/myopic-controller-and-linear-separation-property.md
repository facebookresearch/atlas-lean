# Myopic controller and its linear separation property

Let a controlled neural system evolve as $x_{t+1} = F_t + w_t$ with $F_t = F[x_t, u_t]$, control $u_t \in \mathbb{R}^m$ and noise $w_t \sim \mathcal N(0, Q)$, and let $G_t = G[x_t]$ be a target dynamical system on the same state space. Given a belief distribution over the current state $x_t$, the **myopic controller** chooses $u_t$ to minimize the one-step cost

$$J = \mathbb{E}_x\!\left[\,\|F_t - G_t\|^2\,\right] + \gamma\, u_t^\top u_t, \qquad \gamma > 0,$$

i.e. model-reference control with horizon $1$, so that the controlled system follows the flow of $G$ from wherever it currently is instead of tracking a fixed trajectory (Hocker and Park 2019, Eq. 5).

**Linear case (separation).** If $F_t = Ax_t + Bu_t$ and $G_t = \tilde A x_t$, then

$$J = \operatorname{Tr}\!\left[(A - \tilde A)^\top (A - \tilde A)\Sigma_t\right] + \mu_t^\top(A-\tilde A)^\top(A - \tilde A)\mu_t + 2\mu_t^\top (A - \tilde A)^\top B u_t + u_t^\top (B^\top B + \gamma I_m) u_t,$$

where $\mu_t, \Sigma_t$ are the state mean and covariance, so the optimal control depends on the state distribution only through its mean:

$$u_t^{*} = -\left(B^\top B + \gamma I_m\right)^{-1} B^\top (A - \tilde A)\,\mu_t$$

(Theorem 1). The source's Eq. (8) omits the term $\mu_t^\top(A-\tilde A)^\top(A-\tilde A)\mu_t$, and its Eq. (9) prints $u_t^*=-2(B^\top B+\gamma I_m)^{-1}B^\top(A-\tilde A)\mu_t$ after "Maximizing (8)"; the forms here follow from expanding $\mathbb E\|(A-\tilde A)x_t+Bu_t\|^2$ with $\mathbb E[x_tx_t^\top]=\Sigma_t+\mu_t\mu_t^\top$ and setting the gradient $2B^\top(A-\tilde A)\mu_t+2(B^\top B+\gamma I_m)u_t$ of the convex cost to zero (minimizing, not maximizing). State estimation and control design therefore separate, as in LQG.

**Nonlinear case.** Linearizing $F[x_t, u_t] \approx f_t + B_t u_t$ about null control, with $f_t = F[x_t, 0]$ and $B_t$ the control Jacobian, gives

$$u_t^{*} = -\left(\mathbb{E}_x[B_t^\top B_t] + \gamma I_m\right)^{-1}\mathbb{E}_x\!\left[B_t^\top (f_t - G_t)\right]$$

(Eq. 12), whose expectations are then expanded in the mean and covariance of $x_t$.

## Expansion

Setting $\partial J/\partial u_t = 2(B^\top B + \gamma I)u_t + 2B^\top(A - \tilde A)\mu_t = 0$ gives the linear controller; the covariance enters only through a $u$-independent trace term. The nonlinear formula reduces to the linear one when $f_t = Ax_t$, $B_t = B$ and $G_t = \tilde A x_t$. Because the cost compares one-step dynamics rather than positions along a reference path, a perturbed trajectory is steered through the natural flow of $G$ and may settle in a different attractor than a trajectory-tracking controller would force.

## Sources

- D. Hocker and I. M. Park, *Myopic control of neural dynamics*, PLoS Computational Biology 15(3) (2019), e1006854, Eqs. (5)–(12) and Theorem 1. <https://doi.org/10.1371/journal.pcbi.1006854> (PMCID: PMC6428347)
