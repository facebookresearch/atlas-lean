# Weak-kernel memory model is equivalent to a Keller–Segel system

Let $\Omega$ be a smooth bounded domain, let $G(d_3,x,y,t)$ be the Neumann heat kernel on $\Omega$ with diffusivity $d_3>0$, and let $G_w(t)=\tau^{-1}e^{-t/\tau}$, $\tau>0$, be the weak temporal kernel. Consider the memory-driven movement model

$$\partial_tu=d_1\Delta u+d_2\nabla\cdot(u\nabla v)+f(u),\qquad v(x,t)=\int_{-\infty}^t\!\!\int_\Omega G(d_3,x,y,t-s)\,G_w(t-s)\,u(y,s)\,dy\,ds,$$

with $\partial_nu=0$ on $\partial\Omega$ and history $u=\eta$ for $t\le0$. Then:

1. if $u$ solves this problem, $(u,v)$ solves the Keller–Segel-type system

$$\partial_tu=d_1\Delta u+d_2\nabla\cdot(u\nabla v)+f(u),\qquad \partial_tv=d_3\Delta v+\tau^{-1}(u-v),\qquad \partial_nu=\partial_nv=0,$$

with $v(x,0)=\tau^{-1}\int_{-\infty}^0\int_\Omega G(x,y,-s)e^{s/\tau}\eta(y,s)\,dy\,ds$;

2. conversely, if $(u,v)$ solves that system for all $t\in\mathbb R$, then $u$ solves the memory model with history $\eta(\cdot,s)=u(\cdot,s)$, $s<0$; steady states and periodic solutions correspond.

## Depends on

This node has no prerequisites.

## Proof depends on

Its proof consists of the steps listed under Expansion.

## Expansion

Differentiate $v$ in $t$. The upper limit contributes $G(d_3,x,y,0)G_w(0)u=\tau^{-1}u(x,t)$, since the heat kernel at time $0$ is the Dirac mass. Differentiating the heat kernel gives $d_3\Delta_xG$, hence $d_3\Delta v$, and differentiating $G_w$ gives $-\tau^{-1}G_w$, hence $-\tau^{-1}v$. This is the linear chain trick applied to a space-time kernel. The strong kernel $G_s(t)=t\tau^{-2}e^{-t/\tau}$ leads in the same way to an equivalent three-equation system, so delay models with gamma-distributed memory inherit results from chemotaxis theory. In one space dimension the cell flux $d_1u_x+d_2uv_x$ of the resulting system is the [Keller–Segel flux](../../../../../pattern-formation/turing-instability-with-cross-diffusion/keller-segel-flux.md) with $\chi=-d_2$.

## Sources

- H. Wang, Y. Salmaniw, "Open problems in PDE models for knowledge-based animal movement via nonlocal perception and cognitive mapping", J. Math. Biol. (2023), Section 2.3.2, Equations (2.26)–(2.28), and Appendix A, Lemma A.1, <https://doi.org/10.1007/s00285-023-01905-9>.
