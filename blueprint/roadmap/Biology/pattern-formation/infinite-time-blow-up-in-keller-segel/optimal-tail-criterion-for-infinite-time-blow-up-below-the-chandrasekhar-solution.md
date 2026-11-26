# Optimal tail criterion for infinite-time blow-up below the Chandrasekhar solution

**Model.** The parabolic–elliptic Keller–Segel system in $\mathbb{R}^N$,
$$u_t=\nabla\cdot(\nabla u-u\nabla v),\qquad 0=\Delta v+u,\qquad u(x,0)=u_0(x)\ge 0,$$
with $N\ge 3$ has the singular steady state (Chandrasekhar solution) $U_\infty(r)=(2N-4)/r^2$. Assume $u_0$ is radial, continuous, and lies strictly below it: $0<u_0(r)<U_\infty(r)$ for all $r>0$. Such solutions are global and satisfy $|B_r|^{-1}\int_{B_r}u(\cdot,t)\le 2N/r^2$, but may still become unbounded as $t\to\infty$. For $N\ge 10$ set
$$\lambda_0=\frac{N-2-\sqrt{(N-2)(N-10)}}{2}.$$

**Theorem.**
1. *($N\ge 11$.)* If $\lim_{r\to\infty} r^{2+\lambda_0}\big(U_\infty(r)-u_0(r)\big)=0$, then $\|u(\cdot,t)\|_{L^\infty}\to\infty$ as $t\to\infty$ (blow-up in infinite time). If $\liminf_{r\to\infty} r^{2+\lambda_0}\big(U_\infty(r)-u_0(r)\big)>0$, then $\sup_{t>0}\|u(\cdot,t)\|_{L^\infty}<\infty$.
2. *($N=10$, where $\lambda_0=4$.)* The same dichotomy holds with the weight $r^{2+\lambda_0}$ replaced by $r^{2+\lambda_0}/\log r$.

The thresholds are sharp because the regular radial steady states $U_\alpha$ (with $U_\alpha(0)=\alpha$) approach $U_\infty$ exactly at this rate: $U_\alpha(r)=U_\infty(r)-C_N(\alpha)\,r^{-2-\lambda_0}+o(r^{-2-\lambda_0})$ for $N\ge 11$, with an extra $\log r$ factor when $N=10$, and $C_N(\alpha)=\alpha^{-\lambda_0/2}C_N(1)$.

## Expansion

In terms of the averaged mass $w(r,t)=r^{-N}\int_0^r s^{N-1}u(s,t)\,ds$, the system becomes a scalar semilinear parabolic equation $w_t=\Delta w+(x\cdot\nabla w)w+Nw^2$ posed in $\mathbb{R}^{N+2}$, which enjoys a comparison principle. Steady states correspond to solutions of a Liouville-type equation, and $\lambda_0$ is the smaller root of the indicial equation of its linearization at the singular solution, real exactly when $N\ge 10$. If $u_0$ approaches $U_\infty$ faster than every $U_\alpha$, it eventually lies above each $U_\alpha$ on compacts and is pushed toward $U_\infty$, whose singularity at the origin forces $\|u\|_\infty\to\infty$; if it stays a fixed multiple of $r^{-2-\lambda_0}$ below $U_\infty$, it is trapped under some $U_\alpha$ and stays bounded.

## Sources

- Yūki Naito and Takasi Senba, "Infinite time blow-up of solutions to the classical Keller-Segel model of chemotaxis in higher dimensions", arXiv:2608.29522 (2026), Proposition 1.1, Theorems 1.2–1.3 and the comparison principle Proposition 2.1, <https://doi.org/10.48550/arXiv.2608.29522>.
