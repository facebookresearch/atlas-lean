# Zero-speed threshold for bistable Lotka–Volterra competition fronts

**Model.** Under strong competition ($k_1,k_2>1$) the Lotka–Volterra competition–diffusion system has monotone bistable traveling fronts $(u,v)(t,x)=(U,V)(x+ct)$, $U'>0>V'$, solving

$$U''-cU'+U(1-U-k_1V)=0,\qquad dV''-cV'+rV(1-k_2U-V)=0,\qquad (U,V)(-\infty)=(0,1),\ (U,V)(+\infty)=(1,0),$$

with diffusion ratio $d>0$ and growth ratio $r>0$. The monotone front is unique up to translation and its speed $c=c(d,r,k_1,k_2)$ depends continuously on the parameters. With this convention $c>0$ means the $u$-species invades the region held by $v$, and $c<0$ means the $v$-species invades. Let $\rho=d/r$.

**Maxwell identity.** If a monotone standing front ($c=0$) exists, then

$$3k_1k_2(\rho-1)\,\mathcal E+(k_1-k_2)\big[\rho(k_1-1)+(k_2-1)\big]=0,\qquad \mathcal E=\int_{\mathbb R}(U+V-1)^2U'\,d\xi>0,$$

so $(\rho-1)(k_1-k_2)<0$ unless $\rho=1$ and $k_1=k_2$. For fixed $k_1,k_2>1$ at most one $\rho$ admits a standing front.

**Theorem.** For each $k_2>1$ there is a unique continuous, strictly decreasing $K_{k_2}:(0,\infty)\to(1,\infty)$ with

$$c(d,r,k_1,k_2)=0\iff k_1=K_{k_2}(d/r),\qquad K_{k_2}(1)=k_2,\quad \lim_{\rho\downarrow0}K_{k_2}(\rho)=k_2^2,\quad \lim_{\rho\to\infty}K_{k_2}(\rho)=\sqrt{k_2}.$$

Consequently:

1. if $k_1\ge k_2^2$, then $c<0$ for all $d,r>0$;
2. if $1<k_1\le\sqrt{k_2}$, then $c>0$ for all $d,r>0$;
3. if $\sqrt{k_2}<k_1<k_2^2$, there is a unique $\rho_*(k_1,k_2)$ with $c=0\iff d/r=\rho_*$, and $c>0$ for $d/r<\rho_*$, $c<0$ for $d/r>\rho_*$.

In the symmetric case $k_1=k_2=k>1$: $c=0\iff d=r$ and $\operatorname{sgn}c=\operatorname{sgn}(r-d)$; with $r=1$ and $d>1$ one has $c<0$, so the faster-diffusing species $v$ wins.

## Expansion

Multiplying the standing-wave equations by suitable combinations of $U'$, $V'$ and integrating gives energy identities; eliminating the boundary terms between them yields the Maxwell-type relation, with $\mathcal E$ the only non-explicit quantity. A phase-plane rigidity argument shows that two standing fronts with the same $(k_1,k_2)$ and different $\rho$ cannot coexist, so the zero set of $c$ is a graph $k_1=K_{k_2}(\rho)$; since $c$ is strictly decreasing in $k_1$ (and increasing in $k_2$), this gives the sign on either side. The limits $k_2^2$ and $\sqrt{k_2}$ come from the singular limits $\rho\to0$ and $\rho\to\infty$, where one equation reduces to an algebraic relation and the Maxwell identity can be evaluated.

## Sources

- Shizhao Ma, Dongyuan Xiao, Maolin Zhou, "Propagation Direction of Bistable Traveling Fronts in the Lotka–Volterra Competition–Diffusion System", arXiv:2608.20795 (2026), Theorems 1.1–1.3, Corollaries 1.4–1.5 and Proposition 5.1, <https://doi.org/10.48550/arXiv.2608.20795>.
