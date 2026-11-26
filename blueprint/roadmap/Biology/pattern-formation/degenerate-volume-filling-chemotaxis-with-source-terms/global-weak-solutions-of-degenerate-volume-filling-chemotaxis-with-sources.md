# Global weak solutions of degenerate volume-filling chemotaxis with sources

**System.** Let $\Omega\subset\mathbb R^N$ ($N\ge1$) be a smoothly bounded domain with outer normal $\nu$. For a cell density $u\in[0,1]$ and a signal $v\ge0$ consider

$$
\begin{cases}
u_t=\nabla\cdot\big(D(u,v)\nabla u-h(u,v)\nabla v\big)+f(x,u,v), & x\in\Omega,\ t>0,\\
v_t=\Delta v+g(u,v), & x\in\Omega,\ t>0,\\
\big(D(u,v)\nabla u-h(u,v)\nabla v\big)\cdot\nu=\nabla v\cdot\nu=0, & x\in\partial\Omega,\ t>0,
\end{cases}
$$

under the hypotheses: $D,h,g\in C^2([0,1]\times[0,\infty))$ and $f\in C^2(\overline\Omega\times[0,1]\times[0,\infty))$; $D(1,\cdot)=0$ (diffusion degenerates at the packing limit); $h(0,\cdot)=h(1,\cdot)=0$ and $f(\cdot,0,\cdot)=f(\cdot,1,\cdot)=0$ (volume filling); $D(r,s)\ge D_0(r)>0$ on $[0,1)\times[0,\infty)$ for some $D_0\in C^1([0,1])$; $g(\cdot,0)\ge0$ and $g_s\le\kappa$ for some $\kappa>0$. Examples are $D=(1-u)^2(v+1)$, $h=u(1-u)v$, logistic sources $f=u(1-u)$ or $|x|u(1-u)v$, and either signal production $g=u-v$ or consumption $g=-uv$. Initial data satisfy $u_0\in L^\infty(\Omega)$ with $0\le u_0\le1$, and $v_0\in L^\infty(\Omega)\cap H^2(\Omega)$, $v_0\ge0$, $\nabla v_0\cdot\nu=0$ on $\partial\Omega$.

**Weak solution.** Let $\mathscr D(r,s)=\int_0^rD(\sigma,s)\,d\sigma$. A pair of nonnegative functions $(u,v)$ with $u\le1$,
$u\in C_{\rm w}([0,\infty);L^2(\Omega))\cap L^\infty(\Omega\times(0,\infty))$ and $v\in C([0,\infty);L^2(\Omega))\cap L^2_{\rm loc}([0,\infty);H^2(\Omega))\cap L^\infty_{\rm loc}(\overline\Omega\times[0,\infty))$ is a global weak solution if $\mathscr D(u,v)\in L^2_{\rm loc}([0,\infty);H^1(\Omega))$, $\mathscr D_s(u,v)\nabla v\in L^2_{\rm loc}([0,\infty);L^2(\Omega)^N)$, and for all $T>0$ and $\varphi\in H^1((0,T);H^1(\Omega))$ with $\varphi(T)=0$,

$$
\int_0^T\!\!\int_\Omega\big[-u\varphi_t+(D(u,v)\nabla u-h(u,v)\nabla v)\cdot\nabla\varphi+f(x,u,v)\varphi\big]=\int_\Omega u_0\varphi(0),
$$

together with the analogous identity for $v$; here $D(u,v)\nabla u$ means $\nabla[\mathscr D(u,v)]-\mathscr D_s(u,v)\nabla v$.

**Theorem.** Under these hypotheses a global weak solution exists.

Mass is not conserved because of the source $f$, and the degeneracy $D(1,\cdot)=0$ means no gradient bound on $u$ itself is available; the solution is controlled through $\mathscr D(u,v)$.

## Expansion

One regularizes the degenerate diffusion so that the approximate problems are uniformly parabolic, then proves global existence and the pointwise bounds $0\le u^\varepsilon\le1$ and $v^\varepsilon\ge0$ for the approximations. The bounds on $u^\varepsilon$ come from $h$ and $f$ vanishing at $u=0$ and $u=1$: no flux or source can push the density across these values. Testing the equations gives estimates, uniform in $\varepsilon$, for $\nabla\mathscr D(u^\varepsilon,v^\varepsilon)$, for $v^\varepsilon$ in $L^2H^2$, and for the source terms $f(x,u^\varepsilon,v^\varepsilon)$; the one-sided bound $g_s\le\kappa$ gives local-in-time $L^\infty$ control of $v^\varepsilon$. Compactness, via an Aubin–Lions type argument applied to $\mathscr D(u^\varepsilon,v^\varepsilon)$, gives strong convergence, which identifies the nonlinear terms in the limit.

## Sources

- O. Shibata, "Existence and uniqueness of global weak solutions to degenerate volume-filling chemotaxis systems with source terms", arXiv:2609.29883 (2026), system (1.8) with conditions (1.9)–(1.10), Theorem 1.1, Lemmas 2.1–2.2, Definition 3.1, <https://doi.org/10.48550/arXiv.2609.29883>.
