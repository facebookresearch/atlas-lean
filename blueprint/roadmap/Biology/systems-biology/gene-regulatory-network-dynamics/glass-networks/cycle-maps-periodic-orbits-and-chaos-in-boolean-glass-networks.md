# Cycle maps, periodic orbits and chaos in Boolean Glass networks

**Model.** A Glass network is the piecewise-linear system

$$\dot y_i = -y_i + F_i(\tilde y_1,\dots,\tilde y_n), \qquad \tilde y_i = \begin{cases} 0 & y_i < 0 \\ 1 & y_i > 0\end{cases}, \qquad i = 1,\dots,n,$$

the hard-switching limit of sigmoidal gene-regulatory or neural networks with all thresholds at $0$. It is **Boolean** if every $F_i(\tilde{\mathbf y}) = \pm 1$. Assume $F_i \neq 0$ (Condition 1) and that $F_i$ does not depend on $\tilde y_i$, i.e. no self-input (Condition 2). In the orthant with sign pattern $\tilde{\mathbf y}$, $\mathbf y(t) = \mathbf f + (\mathbf y(0) - \mathbf f)e^{-t}$ moves straight toward the focal point $\mathbf f = \mathbf F(\tilde{\mathbf y})$. If $\mathbf f$ lies outside the orthant, the trajectory crosses a boundary $y_j = 0$, and the boundary-to-boundary map is the fractional-linear map

$$M^{(k)}\mathbf y = \frac{B^{(k)}\mathbf y}{1 + \langle\psi^{(k)},\mathbf y\rangle}, \qquad B^{(k)} = I - \frac{\mathbf f^{(k)}\mathbf e_j^{\top}}{f_j^{(k)}}, \qquad \psi^{(k)} = -\frac{\mathbf e_j}{f_j^{(k)}} .$$

Composing along a cycle of orthants in the state-transition diagram (a directed graph on the $n$-cube) and dropping the coordinate that is zero on the return boundary gives a **cycle map** $M\mathbf y = A\mathbf y/(1 + \langle\phi,\mathbf y\rangle)$ with $A \in \mathbb{R}^{(n-1)\times(n-1)}$.

**Propositions.**
1. $M$ maps rays through the origin to rays and linear subspaces to linear subspaces; under Condition 2 trajectories starting on a common ray converge together as $t \to \infty$.
2. The cone of initial points on the boundary $\mathcal{O}$ that follow the cycle and return to $\mathcal{O}$ is $C = \{\mathbf y \in \mathcal{O} : R\mathbf y \ge 0\}$, with one row of $R$ for each alternative exit variable $y_i^{(k)}$ along the cycle: $R_{i,\cdot} = -\mathbf e_i^{\top}B^{(k)}B^{(k-1)}\cdots B^{(0)}/f_i^{(k)}$.
3. A nonzero fixed point of $M$ in $C$ is a real eigenvector of $A$ with eigenvalue $\lambda > 1$. Conversely, if $\mathbf v \in C$ is a real eigenvector of $A$ with eigenvalue $\lambda > 1$, then $\mathbf y^* = (\lambda - 1)\mathbf v/\langle\phi,\mathbf v\rangle$ is a fixed point of $M$, unique on the span of $\mathbf v$; if $\lambda = 1$ the only fixed point on that span is $0$.
4. The fixed point attached to eigenvalue $\lambda_i$ is asymptotically stable if $\lambda_i > |\lambda_j|$ for all $j \neq i$, neutrally stable if $\lambda_i \ge |\lambda_j|$ with equality for some $j$, and unstable otherwise.
5. The corresponding periodic orbit of the network has period $\log\lambda$.

**Chaos.** For the 4-variable Boolean Glass network

$$\begin{aligned}
\dot y_1 &= -y_1 + 2\tilde y_3 - 1, &\dot y_2 &= -y_2 + 2(1 - \tilde y_3 + \tilde y_1\tilde y_3 - \tilde y_1\tilde y_3\tilde y_4) - 1,\\
\dot y_3 &= -y_3 + 2\big((1-\tilde y_1)(1-\tilde y_4) + \tilde y_2\tilde y_4\big) - 1, &\dot y_4 &= -y_4 + 2\big((1-\tilde y_1)(1-\tilde y_3) + \tilde y_1\tilde y_2\big) - 1,
\end{aligned}$$

the returning cones of two competing cycles and their images under the cycle maps form a Smale horseshoe-like structure, which yields an invariant set $\Lambda$ on which the dynamics are aperiodic and sensitively dependent on initial conditions. That orbits in $\Lambda$ attract nearby trajectories is not proved, and the absence of a stable fixed point or periodic orbit is observed numerically only.

## Proof sketch

Projectively, a fractional-linear map acts on rays as the linear map $A$, so its fixed rays are eigenvectors and the radial coordinate follows a one-dimensional Möbius map whose positive fixed point exists iff $\lambda > 1$; stability on the projective space is decided by the dominance of $\lambda_i$, as in the power method. Each pass through an orthant takes time $\log$ of a ratio of distances to the focal point, and along a periodic orbit these factors multiply to $\lambda$. With four or more variables, branching orthants let one cycle cone stretch across another, which yields the horseshoe.

## Sources

- Roderick Edwards, "Chaos in a continuous-time Boolean network", in G. S. Ladde, N. G. Medhin and M. Sambandham (eds.), *Proceedings of Dynamic Systems and Applications*, vol. 3, Dynamic Publishers, 2001. Preprint version: arXiv:1905.03407 (2019), Sections 2–4 (Conditions 1–2, the boundary maps, Propositions 1–6 and the 4-dimensional example), <https://doi.org/10.48550/arXiv.1905.03407>.
