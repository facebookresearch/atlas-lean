# Spreading–vanishing dichotomy for an invader under a shifting climate

**Model.** An invader $u$ with a Stefan-type free boundary $h(t)$ competes with a native species $v$ on the half-line, while the invader's habitat quality shifts at constant speed $c>0$:
$$u_t=d_1u_{xx}+\bigl(A(x-ct)-b_1u-c_1v\bigr)u,\quad 0<x<h(t),\qquad v_t=d_2v_{xx}+(a_2-b_2u-c_2v)v,\quad x>0,$$
$$u_x(t,0)=v_x(t,0)=0,\qquad u=0\ (x\ge h(t)),\qquad h'(t)=-\mu\bigl(A(h(t)-ct)\bigr)u_x(t,h(t)).$$
Here $A$ is Lipschitz, $A=a_1>0$ on $(-\infty,0]$, $A=a_0<0$ on $[l_0,\infty)$ and decreasing in between, so the favourable region $\{x<ct\}$ advances at speed $c$. Assume weak competition
$$\frac{c_1}{c_2}<\frac{a_1}{a_2}<\frac{b_1}{b_2},$$
with coexistence state $u^*=\frac{a_1c_2-a_2c_1}{b_1c_2-b_2c_1}$, $v^*=\frac{a_2b_1-a_1b_2}{b_1c_2-b_2c_1}$, and let $R^*=\frac\pi2\sqrt{d_1c_2/(a_1c_2-a_2c_1)}$.

**Theorem (dichotomy).** Exactly one of the following occurs:
1. *Spreading:* $h(t)\to\infty$ and $(u,v)\to(u^*,v^*)$ in $C^2_{\rm loc}([0,\infty))$;
2. *Vanishing:* $\lim h(t)\le R^*$, $\|u(t)\|_{C([0,h(t)])}\to0$ and $v\to a_2/c_2$ in $C^2_{\rm loc}$.

**Criteria.** If $h_0\ge R^*$, spreading always happens. For $u_0=\sigma\phi$ there is a sharp threshold $\sigma_0\in(0,\infty]$: vanishing for $\sigma\le\sigma_0$, spreading for $\sigma>\sigma_0$.

**Spreading speed.** If spreading occurs, $\lim_{t\to\infty}h(t)/t=\min\{c,c_0\}$, where $c_0$ is the spreading speed of the homogeneous weak-competition free-boundary problem. The slower of the climate shift and competitive invasion sets the speed.

## Expansion

The invader can only survive where it sees the native species at its competition-reduced level $a_2/c_2$, which makes its effective linear growth rate $a_1-c_1a_2/c_2>0$; $R^*$ is the half-length of the interval on which this rate balances Dirichlet diffusion loss, giving the vanishing bound. Spreading speed selection follows by comparing with semi-wave solutions: if the climate moves slower than $c_0$ the front is pinned to the moving favourable edge (a forced wave), and otherwise it advances at its own semi-wave speed $c_0$.

## Sources

- Phuoc Vinh Dinh, Phuong Le and Tien Dung Nguyen, "Spreading–vanishing dynamics and speed selection in a free-boundary competition model under a shifting climate", arXiv:2609.14679 (2026), Section 1, Theorems 1–3, <https://doi.org/10.48550/arXiv.2609.14679>.
