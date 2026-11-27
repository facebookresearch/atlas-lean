# Global competition outcome in the three-patch Lotka–Volterra stream model

**Model.** Two species with densities $\boldsymbol u = (u_1,u_2,u_3)$ and $\boldsymbol v = (v_1,v_2,v_3)$ live on three patches along a stream (patch $1$ upstream, patch $3$ downstream). They are identical except for their random dispersal rates $d_1, d_2 > 0$ and downstream drift rates $q_1, q_2 > 0$:

$$\begin{aligned}
u_1' &= -(d_1+q_1)u_1 + d_1u_2 + r_1u_1\left(1 - \tfrac{u_1+v_1}{k_1}\right),\\
u_2' &= (d_1+q_1)u_1 - (2d_1+q_1)u_2 + d_1u_3 + r_2u_2\left(1 - \tfrac{u_2+v_2}{k_2}\right),\\
u_3' &= (d_1+q_1)u_2 - d_1u_3 + r_3u_3\left(1 - \tfrac{u_3+v_3}{k_3}\right),
\end{aligned}$$

and the same equations for $\boldsymbol v$ with $(d_2, q_2)$, where $r_i > 0$ and the carrying capacities decrease downstream: $k_1 > k_2 > k_3 > 0$. Each species alone has a unique globally stable positive equilibrium, giving semitrivial equilibria $(\boldsymbol u^*, \boldsymbol 0)$ and $(\boldsymbol 0, \boldsymbol v^*)$.

**Theorem.** Define

$$G_{11} = \left\{(d,q) : d \ge d_1,\ q \ge \tfrac{q_1}{d_1}d\right\}\setminus\{(d_1,q_1)\}, \qquad G_{21} = \left\{(d,q) : 0 < d \le d_1,\ 0 < q \le \tfrac{q_1}{d_1}d\right\}\setminus\{(d_1,q_1)\}.$$

1. If $(d_2, q_2) \in G_{11}$ (species $\boldsymbol v$ disperses more and drifts proportionally more), then $(\boldsymbol u^*, \boldsymbol 0)$ is globally asymptotically stable: $\boldsymbol u$ wins.
2. If $(d_2, q_2) \in G_{21}$, then $(\boldsymbol 0, \boldsymbol v^*)$ is globally asymptotically stable: $\boldsymbol v$ wins.

Moreover there is a continuous invasion curve $q = q^*_{\boldsymbol u}(d)$ through $(d_1, q_1)$ such that $(\boldsymbol u^*, \boldsymbol 0)$ is locally stable when $(d_2,q_2)$ lies above it and unstable when it lies below.

## Expansion

The system is competitive, so by monotone dynamical systems theory the global outcome follows once one semitrivial equilibrium is unstable, the other is stable, and no coexistence equilibrium exists. Stability of $(\boldsymbol u^*, \boldsymbol 0)$ is the sign of the principal eigenvalue $s\big(d_2 D + q_2 Q + \operatorname{diag}(r_i(1 - u_i^*/k_i))\big)$ of the linearization for the invader, where $D$ and $Q$ are the diffusion and drift matrices. Writing $(d_2,q_2) = \mu(1, q_2/d_2)$ and using monotonicity of the principal eigenvalue in $\mu$ (for a fixed drift-to-diffusion ratio) yields the invasion curve. Because favorable habitat is upstream, faster drift is costly: a mutant that drifts more, relative to its diffusion, than the resident cannot invade.

## Sources

- Shanshan Chen, Jie Liu and Yixiang Wu, "On the impact of spatial heterogeneity and drift rate in a three-patch two-species Lotka–Volterra competition model over a stream", Zeitschrift für angewandte Mathematik und Physik 74 (2023), 117, <https://doi.org/10.1007/s00033-023-02009-6>; numbering as in arXiv:2301.06640: Theorem 3.1 and Corollary 3.12.
