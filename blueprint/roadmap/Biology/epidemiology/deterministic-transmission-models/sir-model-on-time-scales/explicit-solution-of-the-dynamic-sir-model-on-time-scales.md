# Explicit solution of the dynamic SIR model on time scales

**Time-scale notation.** On a time scale $\mathbb T$ let $\sigma(t)=\inf\{s\in\mathbb T:s>t\}$, $\mu(t)=\sigma(t)-t$ (graininess), $f^\sigma=f\circ\sigma$, and $f^\Delta$ the delta derivative. A function $p$ is regressive if $1+\mu p\ne0$; then $e_p(\cdot,t_0)$ is the unique solution of $y^\Delta=p\,y$, $y(t_0)=1$, and $p\oplus q=p+q+\mu pq$, $\ominus p=-p/(1+\mu p)$.

**Model.** With rd-continuous rates $b,c:\mathbb T\to\mathbb R_0^+$ and $x(t_0)=x_0>0$, $y(t_0)=y_0>0$, $z(t_0)=z_0\ge0$,

$$x^\Delta=-\frac{b\,x^\sigma y}{x+y},\qquad y^\Delta=\frac{b\,x^\sigma y}{x+y}-c\,y^\sigma,\qquad z^\Delta=c\,y^\sigma .$$

On $\mathbb T=\mathbb R$ this is the SIR model with standard incidence restricted to the active population $x+y$; the shifted terms make each discrete step implicit in the outflow.

**Theorem (explicit solution).** If $f,g$ below are regressive, the unique solution is

$$x(t)=e_{\ominus g}(t,t_0)\,x_0,\qquad y(t)=e_{\ominus(f\oplus g)}(t,t_0)\,y_0,\qquad z(t)=N-e_{\ominus g}(t,t_0)\big[x_0+e_{\ominus f}(t,t_0)\,y_0\big],$$

where $N=x_0+y_0+z_0$, $\kappa=y_0/x_0$ and

$$f(t)=\frac{(c-b)(t)}{1+b(t)\mu(t)},\qquad g(t)=\frac{b(t)\,\kappa}{e_f(t,t_0)+\kappa}.$$

For $x_0,y_0>0$, $z_0\ge0$ one has $x+y+z\equiv N$, $x,y>0$ on all of $\mathbb T$ (since $f,g$ and hence $\ominus g$, $\ominus(f\oplus g)$ are positively regressive), and $z\ge z_0\ge0$ for $t\ge t_0$ because $z^\Delta=c\,y^\sigma\ge0$. Nonnegativity of $z$ is a forward-time statement: for $t<t_0$, $z$ can be negative; on $\mathbb T=\mathbb R$ with $z_0=0$ and $c>0$, $z(t)=-\int_t^{t_0}c\,y\,d\tau<0$.

**Long-time behaviour** ($\mathbb T$ unbounded above).

- If $\int_{t_0}^t f\,\Delta\tau\le l$ for some $l>0$ and all $t\ge t_0$, and $\int_{t_0}^\infty b\,\Delta\tau=\infty$, then $x(t)\to0$ (no susceptibles remain). If in addition $\int_{t_0}^t \ominus f\,\Delta\tau=\int_{t_0}^t\frac{(b-c)(\tau)}{1+c(\tau)\mu(\tau)}\,\Delta\tau\le l'$ for some $l'$ and all $t\ge t_0$, every solution converges to the extinction equilibrium $(0,0,N)$. In particular this holds when $b\equiv c$ (so $f\equiv0$) and $\int b=\infty$.

(The source's Theorem 7 asserts convergence to $(0,0,N)$ under the first two conditions alone: "Under these conditions, all solutions of [the model] converge to the equilibrium $(0,0,N)$". Its proof shows $e_g(t,t_0)\to\infty$, hence $x\to0$, but then reads $y\to0$ off $y=\kappa\,e_{\ominus f}(t,t_0)\,x$ although $e_{\ominus f}=1/e_f$ is not bounded by the hypotheses. Counterexample: $\mathbb T=\mathbb R$, constant $b>0$ and $c\equiv0$ (or $c(t)=e^{-t}$ with $t_0\ge0$) satisfy both conditions, since $\int_{t_0}^t f\,d\tau\le e^{-t_0}$ and $\int b=\infty$; with $c\equiv0$ nobody recovers, so $x+y\equiv x_0+y_0$ and $y\to x_0+y_0>0$, and with $c=e^{-t}$, $z(\infty)\le z_0+(x_0+y_0)\int_{t_0}^\infty e^{-\tau}d\tau<N$, so again $y\not\to0$. The added bound on $\int\ominus f$ gives $e_{\ominus f}(t,t_0)\le e^{l'}$ by the same estimate $e_p\le\exp\int p$ for positively regressive $p$, hence $y\le\kappa e^{l'}x\to0$ and $z\to N$.)
- If $b\le m f$ for some $m>0$ and $\int_{t_0}^\infty f\,\Delta\tau=\infty$, every solution converges to a disease-free equilibrium $(\alpha,0,N-\alpha)$ with $0<\alpha\le N$.

## Expansion

The ratio $w=y/x$ solves a linear dynamic equation with solution $w(t)=\kappa/e_f(t,t_0)=\kappa\,e_{\ominus f}(t,t_0)$, so it decays when $c>b$ and grows when $c<b$. Substituting $y=wx$ makes the susceptible equation linear, $x^\Delta=-\frac{bw}{1+w}\,x^\sigma=-g\,x^\sigma$, whose solution is $x=e_{\ominus g}(t,t_0)x_0$; then $y=wx=e_{\ominus f}e_{\ominus g}y_0=e_{\ominus(f\oplus g)}y_0$ and $z=N-x-y$. On $\mathbb T=h\mathbb Z$ the exponentials become finite products, giving an explicit discrete-time SIR scheme that stays positive for every step size.

## Sources

- M. Lemos-Silva, S. Vaz, D. F. M. Torres, "A consistent SIR model on time scales with exact solution", *Nonlinear Dynamics* 113(25) (2025), 34439–34450, Section 3 (model (dynamic:sir), Theorem 6, Proposition 1, Theorems 7 and 8, Corollaries 1 and 2), <https://doi.org/10.1007/s11071-025-11758-0> (preprint arXiv:2509.22675).
