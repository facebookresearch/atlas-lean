# Exact travelling front for line-supported piecewise-constant production

**Model.** A substance diffuses (coefficient $D$) and degrades (rate $k$) everywhere in the plane but is produced only on the line $y=0$, at a rate that switches on above a threshold $u_c$:

$$
\partial_tu=D\Delta u-ku+a\,\theta(u-u_c)\,\delta(y),\qquad (x,y)\in\mathbb R^2,
$$

with $\theta$ the Heaviside function and $\delta$ the Dirac mass (equivalently, a half-plane problem with the nonlinear flux condition $D\partial_yu+\frac12a\theta(u-u_c)=0$ on $y=0$). It models, for example, a species whose propagules disperse everywhere but establish only along an ecotone edge, or a membrane-catalysed reaction. The rescaling $t\mapsto t/k$, $x_i\mapsto x_i\sqrt{D/k}$, $u\mapsto ua/\sqrt{kD}$ reduces it to

$$
\partial_tu=\Delta u-u+\theta(u-\alpha)\,\delta(y),\qquad \alpha=\frac{u_c}{a}\sqrt{kD}.
$$

A *physical solution* is a continuous tempered distribution $u$ whose trace on the line meets the level $\alpha$ only on a null set and which satisfies the equation in the sense of distributions, the right-hand side being $\theta(u|_{y=0}-\alpha)\otimes\delta(y)$.

**Theorem (stationary state).** For every $\alpha\in(0,1/2)$ the unique nontrivial $x$-independent stationary physical solution is

$$
s(y)=\tfrac12e^{-|y|}.
$$

**Theorem (travelling front).** For every $\alpha\in(0,1/2)$ there is a travelling physical solution $u(t,x,y)=w(x-vt,y)$ with

$$
w(x,y)=\frac1{2\pi}\int_0^\infty K_0\!\Big(\sqrt{(x+\xi)^2+y^2}\,\sqrt{1+\tfrac{v^2}4}\Big)\,e^{-\frac v2(x+\xi)}\,d\xi,\qquad v=2\cot(2\pi\alpha),
$$

where $K_0$ is the modified Bessel function of the second kind of order zero.

## Expansion

For the stationary state, $-s''+s=\theta(s(0)-\alpha)\delta$ forces $s=\frac12e^{-|y|}$ once the line is active, and self-consistency needs $s(0)=\frac12>\alpha$. For the front, the ansatz is that production is on exactly on the half-line $\{x<0,\ y=0\}$ in the moving frame. The profile is then the response of the operator $-\Delta-v\partial_x+1$ to that half-line source: its Green's function is $\frac1{2\pi}e^{-vx/2}K_0(r\sqrt{1+v^2/4})$, and integrating over the source gives $w$. The only remaining condition is continuity of the switch, $w(0,0)=\alpha$; evaluating the integral yields $\alpha=\frac1{2\pi}\operatorname{arccot}(v/2)$, i.e. $v=2\cot(2\pi\alpha)$. This mirrors the McKean-type piecewise-linear reduction of bistable reaction–diffusion fronts, with the nonlocal coupling through the bulk replacing local reaction.

## Sources

- A. S. Zadorin, "Exact travelling solution for a reaction-diffusion system with a piecewise constant production supported by a codimension-1 subspace" (2019), Results, Theorems 1 and 2. <https://doi.org/10.48550/arXiv.1906.00484>
