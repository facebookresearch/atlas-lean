# Global boundedness of two-species attraction–attraction chemotaxis with bilinear boundary influx

**Model.** Two populations $u,w$ attract each other indirectly: $u$ follows a signal $v$ produced by $w$, and $w$ follows a signal $z$ produced by $u$. On a bounded $C^{2+\delta}$ domain $\Omega\subset\mathbb{R}^n$, $n\ge1$,

$$\begin{aligned}u_t&=\Delta u-\chi\nabla\cdot(u\nabla v)+a_1u-b_1u^2-c_1|\nabla u|^2, & \tau v_t&=\Delta v-v+w,\\ w_t&=\Delta w-\xi\nabla\cdot(w\nabla z)+a_2w-b_2w^2-c_2|\nabla w|^2, & \tau z_t&=\Delta z-z+u,\end{aligned}$$

with $\tau\in\{0,1\}$, positive parameters, $\alpha\in[0,1]$, and the boundary conditions

$$u_\nu=(\alpha-1)\chi h_1uv,\quad v_\nu=-h_1v,\qquad w_\nu=(\alpha-1)\xi h_2wz,\quad z_\nu=-h_2z .$$

The Robin conditions on the signals make the chemotactic flux through the boundary nonzero, so for $\alpha>0$ there is a net bilinear inward flux of cells and mass is not conserved. The gradient-dependent terms $-c_i|\nabla\cdot|^2$ model nonlinear dampening.

**Theorem.** There is $C_{\partial\Omega}=C_{\partial\Omega}(\Omega,n)$ such that, for compatible nonnegative $C^{2+\delta}$ initial data, problem admits a unique global classical solution with $0\le u,v,w,z\in L^\infty(\Omega\times(0,\infty))$ provided
1. *(Parabolic–elliptic, $\tau=0$.)* either

$$b_1>c_1+\frac{(\xi\alpha)^2h_2C_{\partial\Omega}}{16c_2},\qquad b_2>c_2+\frac{(\chi\alpha)^2h_1C_{\partial\Omega}}{16c_1}\qquad(\alpha>0),$$

or $\alpha\max\{\chi,\xi\}<\min\{4c_1,4c_2,\tfrac23b_1,\tfrac23b_2\}$;
2. *(Fully parabolic, $\tau=1$.)* the first pair of inequalities holds.

## Expansion

Integrating the $u$ equation, the boundary contributes $\int_{\partial\Omega}(u_\nu-\chi uv_\nu)=\alpha\chi h_1\int_{\partial\Omega}uv\ge0$, an influx that has to be beaten by logistic decay. The boundary integral is controlled through a trace inequality whose constant is $C_{\partial\Omega}$, while the dampening $-c_i|\nabla u|^2$ supplies the gradient terms needed to absorb it; balancing the two is the origin of the explicit thresholds involving $C_{\partial\Omega}/(16c_i)$. An $L^1$ bound then bootstraps through $L^p$ estimates to $L^\infty$. For $\alpha=0$ the net boundary flux of cells vanishes.

## Sources

- Gurusamy Arumugam, Silvia Frassu, Kwancheol Shin and Giuseppe Viglialoro, "Global boundedness of a two-species attraction-attraction chemotaxis model with bilinear boundary influx", arXiv:2607.03306 (2026), the model of Section 2 and Theorems 2.1–2.2, <https://doi.org/10.48550/arXiv.2607.03306>.
