# Instability of boundary mixed steady states in evolutionary games on networks

**Model (evolutionary games on networks, EGN).** Players $v=1,\dots,N$ sit on an undirected graph with adjacency matrix $A=(a_{vw})$; each holds a mixed strategy $x_v\in\Delta_M$ and a payoff matrix $B_v$. With neighbourhood aggregate $k_v(X)=\sum_wa_{vw}x_w$, pure payoffs $p_{v,s}(X)=e_s^TB_vk_v(X)$ and mean payoff $\phi_v=x_v^TB_vk_v$, the dynamics is the networked replicator equation

$$
\dot x_{v,s}=x_{v,s}\big(p_{v,s}(X)-\phi_v(X)\big).
$$

For two strategies (cooperate/defect) with $B_v=\mathrm{diag}(\sigma_{1,v},\sigma_{2,v})$ (no loss of generality) and $x_v\in[0,1]$ the cooperation level,

$$
\dot x_v=x_v(1-x_v)f_v(\mathbf x),\qquad f_v(\mathbf x)=(\sigma_{1,v}+\sigma_{2,v})\sum_wa_{vw}x_w-d_v\sigma_{2,v},
$$

with $d_v$ the degree. A *boundary mixed steady state* has some players pure ($x_v\in\{0,1\}$) and the set $\mathcal M\neq\emptyset$ of others strictly mixed, with $|\mathcal M|<N$; such states have no well-mixed analogue. A *boundary Nash equilibrium* imposes the Nash condition only on mixed players: $x^*_{v,s}>0\Rightarrow p_{v,s}(X^*)\ge p_{v,r}(X^*)$ for all $v\in\mathcal M$.

**Theorem.**

1. Every boundary Nash equilibrium is a steady state. For $M=2$ the converse holds: a profile with $0<|\mathcal M|<N$ is a steady state iff it is a boundary Nash equilibrium. For $M\ge3$ the converse fails.
2. *(Non-interacting mixed players.)* For $M=2$ the set of boundary mixed steady states with a given pure part is convex in the mixed coordinates. If a mixed player $k$ has no mixed neighbours, every value of $x_k$ in $(0,1)$ gives a steady state and $\sigma_{1,k}N_{k,1}=\sigma_{2,k}N_{k,0}$ ($N_{k,1},N_{k,0}$ = numbers of cooperating and defecting neighbours); if $A_{\mathcal M\mathcal M}=0$, steady states come in continua.
3. *(Instability.)* Every boundary mixed steady state of the two-strategy EGN is non-hyperbolic or a saddle; it is never a hyperbolic sink. If $A_{\mathcal M\mathcal M}\neq0$ and the numbers $\sigma_{1,v}+\sigma_{2,v}$, $v\in\mathcal M$, are nonzero with a common sign, the Jacobian has at least one positive and one negative eigenvalue.
4. *(Degeneracy and rank.)* If $A_{\mathcal M\mathcal M}$ is singular, or if $|\mathcal M|>\operatorname{rank}A$, the steady state is non-hyperbolic.

## Expansion

At a boundary mixed steady state, $f_v=0$ for mixed players, so the Jacobian block on mixed coordinates is $J_{\mathcal M\mathcal M}=D\,A_{\mathcal M\mathcal M}$ with $D=\mathrm{diag}\big(x_v(1-x_v)(\sigma_{1,v}+\sigma_{2,v})\big)$, while pure players contribute a triangular block. When the $\sigma$ sums share a sign, $\pm D$ is positive diagonal and, by Sylvester's law of inertia applied to the symmetric $A_{\mathcal M\mathcal M}$, $DA_{\mathcal M\mathcal M}$ has real eigenvalues with the same inertia as $A_{\mathcal M\mathcal M}$. A nonzero symmetric matrix with zero diagonal has trace zero, so it has eigenvalues of both signs: this gives the saddle. Singularity of $A_{\mathcal M\mathcal M}$ or too many mixed players relative to $\operatorname{rank}A$ forces a zero eigenvalue. In contrast with the well-mixed replicator equation, interior-like mixing at the boundary of the network state space is structurally unstable.

## Sources

- Chiara Mocenni, Jean Carlo Moraes, Matheus C. Santos, "On the Structure and Stability of Boundary Mixed Steady States in Evolutionary Games on Networks", arXiv:2606.20688 (2026), Section 2 (Definition 1, Proposition 1, Example 1), Section 3 (Theorem 1, Proposition 2, Lemmas 1–2, Corollary 1, Theorem 2, Corollaries 2–3, Example 2), <https://doi.org/10.48550/arXiv.2606.20688>.
