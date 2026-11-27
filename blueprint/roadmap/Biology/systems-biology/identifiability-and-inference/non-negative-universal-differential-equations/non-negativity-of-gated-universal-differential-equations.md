# Non-negativity of gated universal differential equations

**Setting.** A universal differential equation (UDE) augments a mechanistic ODE with a trainable universal approximator: $\dot x=f(x,t,\theta_M)+U(\cdot,\theta_U)$ on $\mathbb{R}^{n}$, where $f$ encodes known mechanisms and $U$ (for example a feed-forward neural network) models unknown processes. A plain UDE need not keep concentrations or population sizes non-negative even when $f$ does. A *non-negative UDE* (nUDE) gates the learned term state-wise:

$$\dot x=f(x,t,\theta_M)+N(x)\odot U(\cdot,\theta_U),$$

where $\odot$ is the entrywise product, $U$ and $N:\mathbb{R}^n\to\mathbb{R}^n$ are Lipschitz continuous, and $N_i(x)\to0$ as $x_i\to0$ for each $i$ (for instance $N(x)=x$).

**Theorem.** Let $f$ be Lipschitz continuous and leave the non-negative orthant invariant in the sense that $f_i(x,t)\ge0$ whenever $x\ge0$ and $x_i=0$, for every $i$. Then for every non-negative initial condition $x(t_0)\ge0$ the nUDE solution with the same $f$ satisfies $x_i(t)\ge0$ for all $t\ge t_0$ in its interval of existence, for every choice of network parameters $\theta_U$.

## Expansion

The nUDE vector field $g=f+N\odot U$ is Lipschitz, so solutions exist and are unique (Picard-Lindelöf). On the face $\{x\ge0,\ x_i=0\}$ the gate vanishes, $N_i(x)=0$, so $g_i=f_i\ge0$ there: $g$ inherits the quasi-positivity of $f$ on the boundary of the orthant. A Lipschitz field that points into or along the orthant on every boundary face leaves the closed orthant forward invariant (the Nagumo tangency condition). The source argues by contradiction at a first zero crossing of a coordinate, using boundedness of $U$ on the compact time interval to see that $N_iU_i=0$ there. The constraint is an inductive bias built into the model class rather than a penalty, so it holds exactly at every optimizer iterate. In benchmarks on a Lotka-Volterra system and a STAT5 dimerization model, nUDEs removed the negative trajectories that unconstrained UDEs produced, and output regularization of $\int\|N\odot U\|_2\,dt$ reduced absorption of the mechanistic terms by the network.

## Sources

- Maren Philipps, Antonia Korner, Jakob Vanhoefer, Dilan Pathirana, Jan Hasenauer, "Non-Negative Universal Differential Equations With Applications in Systems Biology", *IFAC-PapersOnLine* 58(23) (2024), 25–30, Theorem 1 and Section 3.3 (non-negative UDEs), <https://doi.org/10.1016/j.ifacol.2024.10.005> (preprint arXiv:2406.14246).
