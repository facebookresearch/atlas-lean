# Invasion speed on the cancer stem cell slow manifold

Let $u(x,t)$ and $v(x,t)$ be the densities of cancer stem cells and non-stem tumour cells, $n=u+v$, and let $F:[0,\infty)\to[0,1]$ be a continuous volume-limitation function with $F(0)=1$ and $F(n)=0$ for $n\ge 1$, differentiable on $[0,1]$ with $F'(n)<0$ there (e.g. $F(n)=(1-n)^+$). With stem-cell self-renewal probability $p_s=\varepsilon$, slow motility $D=\varepsilon d$ and tumour-cell death rate $\alpha>0$,

$$u_t=\varepsilon du_{xx}+\varepsilon F(n)u,\qquad v_t=\varepsilon dv_{xx}+(1-\varepsilon)F(n)u+F(n)v-\alpha v .$$

**Slow manifold.** As $\varepsilon\to 0$ the fast dynamics relaxes to

$$M=\{(u,v):\alpha v=F(u+v)(u+v)\},$$

which is the graph of a differentiable function $v_\alpha$ on $[0,1]$ with $v_\alpha(1)=0$. If $\alpha<1$ it starts at $(0,v_\alpha^*)$ where $F(v^*_\alpha)=\alpha$; if $\alpha\ge 1$ it starts at $(0,0)$. Moreover $\alpha_1>\alpha_2$ implies $v_{\alpha_1}(u)<v_{\alpha_2}(u)$ for $u\in(0,1)$, and the total density $n(u)=u+v_\alpha(u)$ is strictly increasing along $M$. On the slow time scale $\tau=\varepsilon t$ the stem cells obey the Fisher–KPP-type equation

$$u_\tau=du_{xx}+F\bigl(u+v_\alpha(u)\bigr)u .$$

**Theorem (invasion paradox).** For a solution of the reduced equation with invasion initial data (monotonically decreasing, tending to $1$ at $-\infty$ and vanishing beyond some $x^*$), $u$ converges to a travelling wave with minimal speed

$$\sigma^*=\begin{cases}2\sqrt{d\alpha},&0<\alpha<1,\\ 2\sqrt d,&\alpha\ge 1.\end{cases}$$

So the invasion speed increases with the death rate of non-stem cells up to $\alpha=1$, and the two branches join continuously.

## Expansion

The reaction term $f(u)=F(u+v_\alpha(u))u$ satisfies $f(0)=f(1)=0$, $f>0$ on $(0,1)$, $f'(1)<0$ and $f'(0)=F(v^*_\alpha)$, which equals $\alpha$ for $\alpha<1$ and $1$ for $\alpha\ge 1$. The front is linearly determined because $f(u)\le f'(0)u$: since $F$ is decreasing, this is equivalent to $n(u)\ge v^*_\alpha=n(0)$, which holds because $n$ is increasing on $M$. The minimal speed is then the linear spreading speed $2\sqrt{df'(0)}$. Biologically, faster death of differentiated cells lowers the slow manifold, so at the leading edge stem cells see less crowding and divide faster.

## Sources

- A. Shyntar, A. Patel, M. Rhodes, H. Enderling, T. Hillen, "The tumor invasion paradox in cancer stem cell-driven solid tumors", Bulletin of Mathematical Biology 84(12) (2022) 139, <https://doi.org/10.1007/s11538-022-01086-4>, PMCID PMC9613767. Eqs. (4)–(11), Lemmas 1–4 and Theorem 1.
