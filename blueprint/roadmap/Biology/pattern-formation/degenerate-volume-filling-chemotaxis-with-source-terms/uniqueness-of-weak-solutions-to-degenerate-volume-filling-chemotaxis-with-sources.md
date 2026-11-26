# Uniqueness of weak solutions to degenerate volume-filling chemotaxis with sources

**Setting.** Consider the degenerate volume-filling chemotaxis system with sources, $u_t=\nabla\cdot(D(u)\nabla u-h(u,v)\nabla v)+f(x,u,v)$, $v_t=\Delta v+g(u,v)$, with no-flux boundary conditions in a smoothly bounded $\Omega\subset\mathbb R^N$, and its global weak solutions as constructed in the depends-on entry, now with signal-independent diffusion $D(r,s)=D(r)$ and $\mathscr D(r)=\int_0^rD(\sigma)\,d\sigma$. Assume in addition $v_0\in W^{2,p}(\Omega)$ for some $p>N$ and the structural conditions: for every $K>0$ there are constants $C_0,\dots,C_3>0$ such that for $(r_i,s_i)\in[0,1]\times[0,K]$ and $x\in\overline\Omega$,

$$
\big(h(r_1,s_1)-h(r_2,s_2)\big)^2\le C_0(r_1-r_2)\big(\mathscr D(r_1)-\mathscr D(r_2)\big)+C_1(s_1-s_2)^2,
$$

$$
\big(f(x,r_1,s_1)-f(x,r_2,s_2)\big)^2\le C_2(r_1-r_2)\big(\mathscr D(r_1)-\mathscr D(r_2)\big)+C_3(s_1-s_2)^2,
$$

and $g(r,s)=g_1(s)+rg_2(s)$ with $g_1,g_2\in C^2([0,\infty))$, $g_1(0),g_2(0)\ge0$, $\max\{g_1',g_2'\}\le C_4$. Examples are $D(u)=(1-u)^2$, $h=u(1-u)^2v$, $f=|x|u(1-u)^2v$, with $g=u-v$ or $g=-uv$.

**Theorem.** Under these assumptions the global weak solution is unique.

The point is that uniqueness holds without mass conservation. Earlier proofs for volume-filling Keller–Segel systems tested the difference $U=u-\hat u$ of two solutions with the solution of the Neumann problem $-\Delta\varphi=U$, which exists only if $\int_\Omega U=0$, a property lost when $f\ne0$.

## Depends on

- [Global weak solutions of degenerate volume-filling chemotaxis with sources](global-weak-solutions-of-degenerate-volume-filling-chemotaxis-with-sources.md)

## Expansion

Let $\mathscr N w$ be the solution of $-\Delta(\mathscr Nw)+\mathscr Nw=w$ with $\nabla(\mathscr Nw)\cdot\nu=0$. It exists for every $w\in L^2(\Omega)$, mean zero or not, and satisfies $\|\mathscr Nw\|_{H^1}\le\|w\|_{L^2}$. Testing the equation for $U=u-\hat u$ with $\mathscr NU$ gives $\langle U_t,\mathscr NU\rangle=\frac12\frac{d}{dt}\|\mathscr NU\|_{H^1}^2$. In the diffusion term, an integration by parts and $\Delta\mathscr NU=\mathscr NU-U$ produce the coercive term $-\int_\Omega U\,(\mathscr D(u)-\mathscr D(\hat u))\le0$ plus a lower-order remainder. The structural conditions bound the taxis and source differences by this coercive quantity plus $\|v-\hat v\|^2$, and Young's inequality absorbs them. The difference $V=v-\hat v$ obeys a linear parabolic inequality driven by $U$, and the $W^{2,p}$ regularity of $v_0$ gives the gradient bounds needed for it. A Gronwall argument on $\|\mathscr NU\|_{H^1}^2+\|V\|_{L^2}^2$, which vanishes at $t=0$, yields $U=V=0$.

## Sources

- O. Shibata, "Existence and uniqueness of global weak solutions to degenerate volume-filling chemotaxis systems with source terms", arXiv:2609.29883 (2026), structural conditions (1.12), Theorem 1.2, Remark 1.1 and Section 4 (proof of uniqueness), <https://doi.org/10.48550/arXiv.2609.29883>.
