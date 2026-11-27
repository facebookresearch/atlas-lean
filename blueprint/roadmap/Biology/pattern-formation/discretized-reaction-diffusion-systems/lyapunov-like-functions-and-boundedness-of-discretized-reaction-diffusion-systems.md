# Lyapunov-like functions and boundedness of spatially discretized reaction-diffusion systems

**Setting.** Divide $[0,1]$ into $n$ compartments of width $h=1/n$. Two species with concentrations $\mathbf{u}=(u_1,\dots,u_n)$ and $\mathbf{v}=(v_1,\dots,v_n)$ react within each compartment and diffuse between neighbors:

$$\dot{\mathbf{u}}=\gamma\,\mathbf{f}(\mathbf{u},\mathbf{v})+\frac{1}{h^2}D\mathbf{u},\qquad \dot{\mathbf{v}}=\gamma\,\mathbf{g}(\mathbf{u},\mathbf{v})+\frac{d}{h^2}D\mathbf{v},$$

where $(\mathbf{f})_i=f(u_i,v_i)$ and $(\mathbf{g})_i=g(u_i,v_i)$, and $D$ is the tridiagonal second-difference matrix with homogeneous Neumann ends (rows $(-1,1)$, $(1,-2,1)$, $(1,-1)$). The constants are $\gamma,d>0$, the functions $f,g$ are $C^1$, $f(0,v)\ge0$ and $g(u,0)\ge0$, and the initial data are nonnegative. Write $\|(u,v)\|=u+v$ for the total concentration.

**Lyapunov-like function (LLF).** A $C^2$ function $W:\mathbb{R}_{\ge0}^2\to\mathbb{R}_{\ge0}$ is an LLF for the reactions if:

- (P1) there is $\underline{K}>0$ with $\nabla W(u,v)\cdot(f(u,v),g(u,v))\le0$ whenever $\|(u,v)\|\ge\underline{K}$;
- (P2) $\partial_{uu}W>0$, $\partial_{vv}W>0$ and $\partial_{uv}W\ge0$ on $\mathbb{R}_{\ge0}^2$;
- (P3) $W(u,v)\to\infty$ as $\|(u,v)\|\to\infty$;
- (P4) level-set tangents do not become vertical or horizontal at infinity: $\sup_{v\ge\underline{v}}|\partial_uW/\partial_vW|<\infty$ for each $u$, and $\sup_{u\ge\underline{u}}|\partial_vW/\partial_uW|<\infty$ for each $v$;
- (P5) for each $v$, either $\lim_{u\to\infty}\partial_uW(u,v)=\infty$, or this limit is finite and $\lim_{u\to\infty}\partial_{uv}W(u,v)$ exists and is finite; the same holds with the roles of $u$ and $v$ exchanged.

**Theorem (boundedness).** If the reactions admit an LLF, then there is $B>0$ such that $\|(u_i(t),v_i(t))\|\le B$ for every compartment $i$ and all $t\ge0$. In particular, solutions exist globally.

**Corollaries.**

- If $W$ is a Lyapunov function for the reactions and is additively separable, $W=w_1(u)+w_2(v)$, with (P2), then $W$ is an LLF. An example is $\alpha u^m+\beta v^p$ with $\alpha,\beta>0$ and $m,p\ge2$.
- No LLF exists if, for some $v\ge0$, $\liminf_{u\to\infty}f(u,v)>0$ and $|f(u,v)/g(u,v)|\to\infty$ as $u\to\infty$, or if the symmetric condition holds with $u$ and $v$ exchanged.

**Examples.**

- The Schnakenberg kinetics $f=a-u+u^2v$, $g=b-u^2v$ show diffusion-driven (Turing) instability, but they have the LLF $W=u+2v+c/(u+1)+1/(v+1)$ for a suitable $c>0$. The discretized system is therefore bounded.
- The strongly mutualistic Lotka–Volterra system $f=u(a_1-b_1u+c_1v)$, $g=v(a_2+b_2u-c_2v)$ with $b_2c_1>b_1c_2$ has no LLF.
- The reactions $f=uv(u-v)(u+1)-\delta u$, $g=uv(v-u)(v+1)-\delta v$ have a globally stable origin, yet no LLF exists. With two compartments and small $\delta$ the discretized system is unbounded, so diffusion-driven blow-up occurs.

## Expansion

The usual Lyapunov argument fails because diffusion moves mass between compartments and can push an individual compartment uphill in $W$. Instead, fix a level $K\ge\max\{\underline{K},\underline{u},\underline{v}\}$ such that $\max_{\|(u,v)\|=L}W<\max_{\|(u,v)\|=K}W=:M^{(K)}$ for every $L<K$. Then track

$$\mathcal{W}(t)=n_tM^{(K)}+\sum_{i\notin\Omega_K(t)}W(u_i,v_i),$$

where $n_t$ counts the compartments inside $\Omega_K=\{\|(u,v)\|<K\}$. Convexity (P2) makes the diffusion contribution to $\frac{d}{dt}\sum W$ nonpositive up to boundary-flux terms. Properties (P4) and (P5) bound those terms through the slopes of the level sets. While some compartment exceeds a threshold $\underline{C}$, (P1) then makes $\mathcal{W}$ nonincreasing across every interval between crossings of $\partial\Omega_K$. As a result, $\sum_iW(u_i,v_i)\le n\max_{\|(u,v)\|=\underline{C}}W$ for all time, and (P3) turns this into a uniform bound $B$. The obstruction corollary works because a reaction field that points outward in $u$ with vanishing relative $v$-component cannot satisfy (P1) and (P4) together. A continuous reaction-diffusion system can blow up even when the discretized one stays bounded, so the discrete system must be analyzed on its own terms.

## Sources

- Jacqueline M. Wentz and David M. Bortz, "Boundedness of a Class of Spatially Discrete Reaction-Diffusion Systems", SIAM Journal on Applied Mathematics 81 (2021), 1870–1892, <https://doi.org/10.1137/20m131850x>; numbering as in arXiv:1903.09680: Section 2 (definition of the Lyapunov-like function, properties (P1)–(P5) and secondary properties (C1)–(C5)), Section 3 (main boundedness theorem), Section 4 (corollaries on Lyapunov functions that are LLFs and on nonexistence of LLFs; Schnakenberg, mutualistic and Weinberger examples), with proofs in the appendices.
