# Optimal radiotherapy control of a Fisher-KPP brain-tumour model

**Model.** On a bounded domain $\Omega\subset\mathbb{R}^d$, $d\in\{1,2,3\}$, the tumour cell density $u(x,t)$ (normalized by the carrying capacity) solves

$$u_t-\nabla\cdot\bigl(D(x)\nabla u\bigr)=a(x,t)\,u(1-u)\ \ \text{in }\Omega_T,\qquad \nabla u\cdot\mathbf{n}=0\ \ \text{on }\partial\Omega\times(0,T),\qquad u(\cdot,0)=u_0,$$

with heterogeneous diffusivity $D\in L^\infty(\Omega)$, $D\ge d_0>0$ (grey versus white matter), and net growth rate $a(x,t)=\rho-R(x,t)$, where $\rho>0$ is the proliferation rate and $R\ge0$ the radiotherapy kill rate; $a$ may change sign.

**Theorem (well-posedness).**

1. For nonnegative $u_0\in L^2(\Omega)$ and $a\in L^\infty$, there is a unique nonnegative weak solution on some interval $(0,T^*)$, with $T^*$ depending only on $\|u_0\|_{L^2}$, $\|a\|_{L^\infty}$, $|\Omega|$, $d$ and $d_0$.
2. If moreover $u_0\in L^\infty(\Omega)$, the solution is bounded on some $(0,T^{**}]$, and higher regularity holds for smoother data.
3. If $a\ge0$ (i.e. $R\le\rho$), these local results hold on every finite interval $(0,T)$, and $0\le u_0\le1$ implies $0\le u\le1$: the biologically relevant set is invariant.

**Theorem (optimal radiotherapy).** Fix a dose cap $M>0$ and a total dose $\Gamma>0$ with $0<\Gamma/M\le T|\Omega|$, and let

$$\mathcal{U}=\Bigl\{R\in L^\infty(\Omega_T): 0\le R\le M,\ \int_0^T\!\!\int_\Omega R\,dx\,dt=\Gamma\Bigr\},\qquad J(R)=\int_0^T\!\!\int_\Omega u_R\,dx\,dt,$$

the cumulative tumour burden. Assume the hypotheses of item 2, with $T\le T^{**}$ of item 2 unless $M\le\rho$ or $u_0$ satisfies $0\le u_0\le1$ and $\int_\Omega(|\ln u_0|+|\ln(1-u_0)|)\,dx<\infty$ (the source's (3.3)), in which case any $T>0$ is allowed. Then an optimal dose distribution $R^*\in\mathcal{U}$ minimizing $J$ exists. If $u^*$ is the optimal state and $\Phi\ge0$ the bounded weak solution of the backward adjoint problem

$$\Phi_t+\nabla\cdot(D\nabla\Phi)+(\rho-R^*)(1-2u^*)\Phi=-1,\qquad \nabla\Phi\cdot\mathbf{n}=0,\qquad \Phi(\cdot,T)=0,$$

then, with $g=\Phi\,u^*(u^*-1)$,

$$\int_0^T\!\!\int_\Omega R^*g\,dx\,dt\ \le\ \int_0^T\!\!\int_\Omega R\,g\,dx\,dt\qquad\text{for all }R\in\mathcal{U}.$$

So $R^*$ minimizes the linear functional $R\mapsto\int_0^T\!\int_\Omega Rg$ over $\mathcal U$, and hence there is a threshold $\lambda^*$ with $R^*=M$ almost everywhere on $\{g<\lambda^*\}$ and $R^*=0$ almost everywhere on $\{g>\lambda^*\}$. Since $g\le0$ where $0\le u^*\le1$, the dose is concentrated, at the maximal rate $M$, where $\Phi\,u^*(1-u^*)$ is largest, subject to the total-dose budget. It is bang-bang when the level set $\{g=\lambda^*\}$ has measure zero; on a level set of positive measure the condition leaves the dose free. For instance, if $u_0\equiv0$ then $u_R\equiv0$ and $J\equiv0$, so every $R\in\mathcal U$ is optimal.

## Expansion

1. Local existence uses a Faedo-Galerkin scheme with energy estimates; nonnegativity and uniqueness follow from energy estimates on the negative part and on the difference of two solutions.
2. For $L^\infty$ data further a priori estimates give local boundedness; when $a\ge0$, the constants $0$ and $1$ act as sub- and supersolutions, which gives the invariant region and global existence.
3. Existence of an optimal control: $J$ is bounded below, a minimizing sequence has a weak-$*$ limit in the convex, weak-$*$ closed set $\mathcal{U}$, and the states converge strongly by compactness, so the limit is optimal.
4. The sensitivity $\psi=\lim_{\varepsilon\to0}(u_{R^*+\varepsilon r}-u^*)/\varepsilon$ solves a linearized equation with source $-r\,u^*(1-u^*)$; pairing it with $\Phi$ turns $\frac{d}{d\varepsilon}J\ge0$ into the stated inequality.

## Sources

- M. Chugunova, H. Ji, R. Taranets, N. Vasylyeva, *Analysis of a radiotherapy model for brain tumors*, arXiv:2409.17903 (Section 3, local solvability, local regularity, higher regularity and global solvability theorems; Section 8, existence of the optimal control and the necessary optimality condition). <https://doi.org/10.48550/arXiv.2409.17903> Published version: Studies in Applied Mathematics 155 (2025) e70074, <https://doi.org/10.1111/sapm.70074>.
