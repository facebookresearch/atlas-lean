# Martingale solutions of the stochastic porous-medium Keller–Segel system with power-law sensitivity

**Setting.** Let $\mathcal O\subset\mathbb R$ be a bounded interval, $T>0$, $\chi>0$, and write $s^{[m]}=|s|^{m-1}s$. Consider the cell density $u$ and chemoattractant $v$ governed by

$$du=\big(\Delta(u^{[m]})-\chi\,\nabla\cdot(u\,\nabla v^{[a]})\big)\,dt+u\,dW(t),\qquad -\Delta v=u-v\quad\text{in }\mathcal O\times(0,T],$$

with homogeneous Neumann conditions $\partial_n u=\partial_n v=0$ on $\partial\mathcal O$ and $u(0)=u_0$. Here $\Delta u^{[m]}$ is porous-medium (crowding) diffusion, $\nabla\cdot(u\nabla v^{[a]})$ is a Stevens power-law chemotactic response, and $W$ is a cylindrical Wiener process on $L^2(\mathcal O)$ (multiplicative environmental noise). A *martingale solution* is a filtered probability space, a cylindrical Wiener process on it and a progressively measurable $H^{-1}_2(\mathcal O)$-valued process $u$ (with the corresponding $v$) solving the system weakly.

**Theorem.** Assume $a\ge1$ and

$$m\ge 2a+1 .$$

Let $u_0\in H^{-1}_2(\mathcal O)$ with $\mathbb E\,\|u_0\|_{L^{m+1}}^{m+1}<\infty$.

1. (Global existence) For every $T>0$ there is a martingale solution on $[0,T]$, and a constant $C$ depending only on the data and parameters with

$$\mathbb E\Big[\sup_{t\le T}\|u(t)\|_{H^{-1}_2}^2+4\int_0^T\|u(t)\|_{L^{m+1}}^{m+1}\,dt\Big]\le C,$$

together with a uniform-in-time bound on $\mathbb E\sup_{t\le T}\|u(t)\|_{L^{m+1}}^{m+1}$.
2. (Non-negativity) If in addition $u_0\ge0$ almost surely, then $u(t,x)\ge0$ for $dt\otimes dx\otimes d\mathbb P$-almost every $(t,x,\omega)$.

The threshold $m\ge 2a+1$ expresses a balance: a stronger chemotactic response (larger $a$) needs stronger nonlinear diffusion to prevent aggregation from overwhelming dispersal.

## Expansion

Freeze the chemotactic drift: for a given process $\xi$ in a closed ball $\mathbb X(R_1,R_2)$ of a path space, the decoupled equation $du=(\Delta u^{[m]}-\chi\nabla\cdot(u\nabla v_\xi^{[a]}))dt+u\,dW$ is a monotone SPDE in the Gelfand triple $L^{m+1}\subset H^{-1}_2\subset(L^{m+1})^*$ and has a unique solution. Energy estimates in $H^{-1}_2$ and $L^{m+1}$ show that the solution map $\xi\mapsto u$ sends the ball into itself (this is where $m\ge 2a+1$ lets the diffusion dissipation absorb the drift), is continuous, and has time-Hölder bounds in $H^{-1}_2$ giving compactness. A stochastic Schauder–Tychonoff fixed-point argument then yields a martingale solution. Non-negativity follows from an Itô-formula estimate for the negative part $u^-$.

## Sources

- Yiming Jiang, Haohang Li, Yawei Wei, "Stochastic Keller Segel System with Porous Medium Diffusion and Nonlinear Chemotactic Sensitivity", arXiv:2608.04614 (2026), system (1.1), Definition 2.3, Theorem 3.1, Lemma 3.2, Propositions 3.3–3.5 and Theorem 4.1, <https://doi.org/10.48550/arXiv.2608.04614>.
