# The linear feedback attains the Riccati value

Under the hypotheses of the [lower bound](lqr-cost-ge.md), for every horizon $T$ and initial state $x_0$ the linear state feedback

$$
u_t = -K_{T-1-t}\, x_t, \qquad K_j = (R + B^\top M_j B)^{-1} B^\top M_j A,
$$

attains $J_T(x_0, u) = x_0^\top M_T x_0$. With the lower bound, the linear feedback is optimal among all control sequences, and the optimal cost is the quadratic form of $M_T$.

Proof: by induction on $T$, using [the Bellman cost of the linear control](bellman-cost-neg-gain.md) at each step.

## Sources

- B. Recht, *A tour of reinforcement learning: the view from continuous control*, Annual Review of Control, Robotics, and Autonomous Systems 2 (2019), arXiv:1806.09460, Section 4 ("the control action is a linear function of the state $u_t = -K_t x_t$ for some matrix $K_t$ that can be computed via a simple linear algebraic recursion"), for the deterministic version of problem (4.1).
