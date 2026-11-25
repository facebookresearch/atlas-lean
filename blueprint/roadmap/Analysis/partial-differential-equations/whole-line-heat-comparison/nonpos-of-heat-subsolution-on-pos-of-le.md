# Heat maximum principle on the positive set

Let $\nu\ge0$ and $T\in\mathbb R$. The real field $u$ is jointly continuous on
$[0,T]\times\mathbb R$, has $C^2$ spatial slices at every $0<t\le T$, and has an
actual left time derivative $u_t(t,x)$ there. More precisely the derivative is
within $(-\infty,t]$; no initial-time derivative is required. Suppose there are
$M,c\ge0$ with the one-sided bound $u(t,x)\le M e^{c|x|}$ uniformly on the closed
strip, and $u(0,x)\le0$ for all $x$.

Require the heat-residual inequality only where the field is positive:

$$
0<u(t,x)\quad\Longrightarrow\quad
u_t(t,x)-\nu\partial_x^2u(t,x)\le0\qquad(0<t\le T).
$$

Then $u(t,x)\le0$ throughout the closed strip. The initial and terminal times
are included, and zero diffusivity is allowed. The condition is weaker than
requiring a heat subsolution everywhere: a negative field may have positive
heat residual. Subtracting a small positive exponential spatial barrier gives
a strict contradiction at a positive maximum on a compact rectangle; the
one-sided growth bound removes the artificial lateral boundaries.

## Sources

The maximum-principle background is Stanford Math 220B, [*Heat Equation*](https://web.stanford.edu/class/math220b/handouts/heateqn.pdf), Theorems 18 and 20, and James Nolen, [*Partial Differential Equations and Diffusion Processes*](https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf), §2.8. The exponential spatial barrier and exponential time factor derive the stated whole-line potential results; these references are not asserted to state exactly this linear-exponential growth class and endpoint formulation.
