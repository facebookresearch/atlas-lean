# Local null controllability of parabolic–elliptic chemotaxis by Neumann boundary control

**System.** On an interval $(0,\mathrm L)$ and time horizon $T>0$, a density $w$ is advected by a drift depending on an elliptic signal $u$:
$$w_t = w_{xx} + f(u)\,w_x, \qquad 0 = u_{xx} - u - w \quad \text{in } (0,T)\times(0,\mathrm L),$$
$$w_x(t,0) = g(t), \quad w_x(t,\mathrm L) = 0, \quad u_x(t,0) = u_x(t,\mathrm L) = 0, \quad w(0,\cdot) = w_0,$$
with $f:\mathbb R\to\mathbb R$ locally Lipschitz and a single scalar control $g$ acting through the Neumann condition at the left endpoint. Equivalently $u = -(I - \partial_{xx,N})^{-1}w$, so the drift is nonlocal in space.

**Theorem.** There is $c_1 > 0$, depending on $\mathrm L$ and $f$ but not on $T$, such that for every $T>0$ and every $w_0 \in L^\infty(0,\mathrm L)$ with
$$\|w_0\|_{L^\infty(0,\mathrm L)} \le \exp\!\big(-c_1(1 + T + 1/T)\big),$$
there is a control $g \in L^\infty(0,T)$ for which the system has a weak solution with $w(T) = 0$ in $L^2(0,\mathrm L)$; moreover $u \in C([0,T];H^2(0,\mathrm L))$ and $u(T) = 0$.

**Linear step.** For any bounded drift coefficient $B \in L^\infty$, the linear problem $w_t = w_{xx} + B w_x$ with the same boundary control is null controllable with a bounded control satisfying $\|g\|_{L^\infty(0,T)} \le e^{C\kappa}\|w_0\|_{L^2}$, where $\kappa$ grows like $1 + 1/T + M^2 + TM^2$ with $M = \|B\|_{L^\infty}$. This rests on an observability inequality for the adjoint,
$$\|\varphi(0)\|_{L^2(I)}^2 \le \exp\!\big(C(1 + 1/T + M^2 + TM^2)\big)\int_0^T\!\!\int_{\tilde\omega}|\varphi|^2\,dx\,dt,$$
proved by a Carleman estimate on an extended interval $I \supset (0,\mathrm L)$.

## Expansion

The linear equation is extended to a larger interval by an even extension of the initial datum and an odd extension of the drift; an internal $L^2$ control supported in the added piece drives the extended state to zero, and its restriction yields a boundary control on $(0,\mathrm L)$, with a heat-kernel estimate bounding the needed derivative trace in $L^\infty$. The nonlinear result then follows from a set-valued fixed point argument with $B = f(u)$, which closes because small data keep $u$, hence $f(u)$, uniformly bounded.

## Sources

- Mohmedmunavvar Mubarak Bapu, "Local null controllability of a parabolic-elliptic chemotaxis system by a Neumann boundary control", arXiv:2611.02621 (2026), Theorem 1.1, Theorem 3.1, Theorem 3.2 (Carleman estimate) and Proposition 3.1 (observability inequality), <https://doi.org/10.48550/arXiv.2611.02621>.
