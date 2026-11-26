# Global boundedness of tumour–immune chemotaxis in one dimension

**Model.** On a bounded smooth domain $\Omega\subset\mathbb{R}^n$ with homogeneous no-flux boundary conditions, tumour density $u$, immune effectors $v$ and chemokine $w$ satisfy

$$
\begin{aligned}
u_t&=d_1\Delta u+u(1-u-v),\\
v_t&=d_2\Delta v-\xi\nabla\cdot(v\nabla w)+\sigma_0+\sigma_1\frac{w}{1+w}-\delta v-\beta uv,\\
w_t&=d_3\Delta w+\alpha u+\gamma uv-\ell w,
\end{aligned}
$$

with $d_1,d_2,d_3,\delta,\ell>0$ and $\xi,\sigma_0,\sigma_1,\beta,\alpha,\gamma\ge0$.

**Statement.** For nonnegative initial data:
1. the classical solution stays nonnegative and $0\le u\le M_u:=\max\{1,\|u_0\|_{L^\infty}\}$ on its maximal interval;
2. if $\gamma=0$ (no interaction-induced chemokine production), then in every dimension $n\ge1$ the solution is global and uniformly bounded, with $0\le w\le\max\{\|w_0\|_{L^\infty},\alpha M_u/\ell\}$ and $\sup_{t>0}\|v(\cdot,t)\|_{L^\infty}<\infty$;
3. if $n=1$ and $\Omega=(0,L)$, the solution exists for all $t>0$ for any $\gamma\ge0$ and $\sup_{t>0}\big(\|u\|_{L^\infty}+\|v\|_{L^\infty}+\|w\|_{L^\infty}\big)<\infty$.

In two dimensions with $\gamma>0$ the same estimates close when $\xi$ is small relative to $d_2,d_3,\ell,\gamma,M_u$; unconditional two-dimensional boundedness for $\gamma>0$ is left open.

## Expansion

The tumour bound is a comparison with the logistic ODE, since $-uv\le0$. With $\gamma=0$ the chemokine equation is linear with source $\alpha u\le\alpha M_u$, so the maximum principle bounds $w$, and parabolic regularity bounds $\nabla w$ in every $L^q$; the effector equation is then a linear drift–diffusion equation with bounded coefficients, and Moser–Alikakos iteration gives $v\in L^\infty$. When $\gamma>0$ the chemokine source $\gamma uv$ feeds back on the chemotactic drift; in one dimension the $L^1$ bound on $v$ (from mass balance) plus Sobolev embedding $W^{1,1}\subset L^\infty$ suffices to control $w_x$ and close the bootstrap, while in higher dimension this is the usual obstruction for signal-production chemotaxis with only linear damping.

## Depends on

- [Tumour-free threshold of a chemotactic tumour–immune model](tumour-free-threshold-of-a-chemotactic-tumour-immune-model.md)

## Sources

- Jiguang Yu, Louis Shuo Wang, "Spatially Limited Immune Access Creates Tumour Refugia in Hepatocellular Carcinoma", arXiv:2609.27949: Section 2 (core model); Appendix A: Propositions A.1–A.3, Theorem A.4 (global existence and boundedness in one dimension) and the remark on two dimensions. <https://doi.org/10.48550/arXiv.2609.27949>
