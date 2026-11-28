# Invariant density of the continuous bursting PDMP

**Model.** The amount $Y(t)>0$ of a gene product decays deterministically by $\dot y=-\gamma(y)$ and jumps up at random times with state-dependent intensity $\varphi(y)$; at a jump from $y$ a burst of size $e$ is added with density $h(\cdot,y)$, $\int_0^\infty h(x,y)\,dx=1$. Densities $u(t,x)$ evolve by

$$\partial_t u=\partial_x\big(\gamma(x)u\big)-\varphi(x)u+\int_0^x\varphi(y)\,u(t,y)\,h(x-y,y)\,dy .$$

Assume $\gamma$ is continuous and positive on $(0,\infty)$, $\varphi\ge0$ with $\varphi/\gamma$ locally integrable, and for some $\delta>0$

$$\int_0^\delta\frac{dx}{\gamma(x)}=\infty,\qquad \int_0^\delta\frac{\varphi(x)}{\gamma(x)}\,dx=\infty .$$

Set $Q(x)=\int_x^{\bar x}\varphi(y)/\gamma(y)\,dy$ and let $K$ be the transition operator of the post-jump chain $Y(t_k)$,

$$Kv(x)=\int_0^x h(x-z,z)\,\frac{\varphi(z)}{\gamma(z)}\,e^{-Q(z)}\int_z^\infty v(y)\,e^{Q(y)}\,dy\,dz .$$

**Theorem.**

*(1)* The associated substochastic semigroup $\{P(t)\}$ on $L^1(0,\infty)$ has at most one invariant density, and it is stochastic whenever $K$ is mean ergodic.

*(2)* *(Correspondence.)* If $u^*\ge0$ with $\varphi u^*\in L^1$ solves $\gamma(x)u^*(x)=\int_0^x\overline H(x-y,y)\varphi(y)u^*(y)\,dy$, where $\overline H(x,y)=\int_x^\infty h(z,y)\,dz$, then $v^*(x)=\int_0^xh(x-y,y)\varphi(y)u^*(y)\,dy$ is a fixed point of $K$; conversely a nonnegative fixed point $v^*$ of $K$ yields such a $u^*$ via the formula below.

*(3)* *(Asymptotic stability.)* If $K$ has an invariant density $v^*>0$ a.e. and

$$c:=\int_0^\infty\frac{1}{\gamma(x)}\int_x^\infty e^{Q(y)-Q(x)}v^*(y)\,dy\,dx<\infty,$$

then $P(t)$ is stochastic and $\|P(t)v-u^*\|_{L^1}\to0$ for every initial density $v$, where

$$u^*(x)=\frac{1}{c\,\gamma(x)}\int_x^\infty e^{Q(y)-Q(x)}\,v^*(y)\,dy$$

is the unique stationary density.

**Exponential bursts.** If $h(x,y)=b^{-1}e^{-x/b}$, then $v^*(x)=e^{-x/b-Q(x)}$ is a fixed point of $K$, and if $c=\int_0^\infty\gamma(x)^{-1}e^{-x/b-Q(x)}dx<\infty$ and $\int_0^\infty e^{-x/b-Q(x)}dx<\infty$, every density converges in $L^1$ to

$$u^*(x)=\frac{1}{c\,\gamma(x)}\,e^{-x/b-Q(x)} .$$

## Expansion

The divergence of $\int_0\varphi/\gamma$ ensures that from every state a jump occurs in finite time, so the post-jump chain is well defined and solves the stochastic recurrence $Y(t_k)=Q^{-1}(Q(Y(t_{k-1}))+\varepsilon_k)+e_k$ with $\varepsilon_k$ standard exponential. Uniqueness of the invariant density comes from strict positivity of the resolvent near $0$: for two distinct densities the $L^1$ contraction is strict. Mean ergodicity of $K$ implies the semigroup is stochastic (non-explosive), by the Tyran-Kamińska theory of substochastic semigroups attached to jump processes. Fixed points of $K$ (the law right after a burst) and invariant densities of the semigroup are related by integrating the flow between jumps, which gives the formula for $u^*$. Finally $P(t)$ is partially integral and has a unique positive invariant density, so the Pichór–Rudnicki theorem gives asymptotic stability. In the exponential case the explicit fixed point recovers the gamma-like stationary density, now with a convergence guarantee.

The general statement collects the propositions and main theorem of the section on the continuous bursting model of the source; the exponential case is the first corollary of its subsection on exponential burst sizes.

## Sources

- M. C. Mackey, M. Tyran-Kamińska, R. Yvinec, *Dynamic behavior of stochastic gene expression models in the presence of bursting*, SIAM J. Appl. Math. 73 (2013); arXiv:1301.1797. <https://doi.org/10.48550/arXiv.1301.1797>
