# Global boundedness and stabilization in the alopecia areata chemotaxis model

**Model.** In alopecia areata, CD4$^+$ T cells ($u$) and CD8$^+$ T cells ($v$) migrate up gradients of the cytokine IFN-$\gamma$ ($w$), which both populations produce and which in turn drives their proliferation. On a smooth bounded domain $\Omega \subset \mathbb{R}^2$ with homogeneous Neumann conditions, with weakly singular sensitivity $\chi_i/w^k$:

$$\begin{aligned}
u_t &= \Delta u - \chi_1\nabla\cdot\Big(\frac{u}{w^k}\nabla w\Big) + w - \mu_1u^2,\\
v_t &= \Delta v - \chi_2\nabla\cdot\Big(\frac{v}{w^k}\nabla w\Big) + w + ruv - \mu_2v^2,\\
w_t &= \Delta w + u + v - w,
\end{aligned}$$

with $\chi_1,\chi_2,\mu_1,\mu_2,r > 0$ and $k \in (0,1)$. Initial data: $u_0, v_0 \in C^0(\overline{\Omega})$ nonnegative with $u_0 \not\equiv 0$, and $w_0 \in W^{1,\infty}(\Omega)$ nonnegative.

**Theorem.**
1. (Boundedness) The system has a unique global classical solution, and there is $C > 0$ with $\|u(\cdot,t)\|_{L^\infty} + \|v(\cdot,t)\|_{L^\infty} + \|w(\cdot,t)\|_{W^{1,\infty}} \le C$ for all $t > 0$, for all sensitivities $\chi_1,\chi_2 > 0$.
2. (Stabilization) If $\mu_1 < \mu_2 < 3\mu_1$ and $r = \mu_2 - \mu_1$, then the solution converges in $L^\infty(\Omega)$ to the homogeneous steady state
$$u_* = v_* = \frac{2}{\mu_1}, \qquad w_* = \frac{4}{\mu_1}.$$
3. (Exponential rate) Under the same conditions, there are $C, \lambda > 0$ with $\|u - u_*\|_{L^\infty} + \|v - v_*\|_{L^\infty} + \|w - w_*\|_{L^\infty} \le Ce^{-\lambda t}$ for $t > 0$.

## Expansion

At $u_* = v_* = 2/\mu_1$, $w_* = 4/\mu_1$ one checks $w_* = \mu_1u_*^2$, $w_* + ru_*v_* = \mu_2v_*^2$ (using $r = \mu_2-\mu_1$) and $w_* = u_* + v_*$. Boundedness comes from the energy $\int u\ln u + \int v\ln v - \lambda\int u\ln w - \lambda\int v\ln w + \frac12\int|\nabla w|^2$, which gives $L\ln L$ bounds on both populations without a lower bound for $w$; the weak singularity $k < 1$ and the logistic terms then allow passage to $L^p$ and $L^\infty$ bounds in two dimensions. Convergence uses a Lyapunov functional of entropy type around $(u_*,v_*,w_*)$, whose dissipation is coercive in the stated parameter window.

## Sources

- Pengxue Xiang, Yuebo Cao and Hongying Yang, "Global boundedness and asymptotic behavior of the chemotaxis system for Alopecia Areata with weakly singular sensitivity", arXiv:2604.26905 (2026), Section 1, Theorems 1.1 and 1.2, <https://doi.org/10.48550/arXiv.2604.26905>.
