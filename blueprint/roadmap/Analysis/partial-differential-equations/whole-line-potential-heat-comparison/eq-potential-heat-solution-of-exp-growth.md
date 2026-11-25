# Identification with the actual potential-heat construction

Let $\nu>0$, and let $g:\mathbb R\to\mathbb R$ be continuous with exponential
growth $|g(x)|\le A e^{c|x|}$ for some $A,c\ge0$. For every $s\in[0,T]$, suppose
$q(s,\cdot)\in C^2(\mathbb R)$. For each $j=0,1,2$, its actual spatial derivative
$\partial_x^j q$ is jointly continuous on $[0,T]\times\mathbb R$ and has a uniform
finite absolute bound there; the bounds may differ by order. No time derivative
of $q$ and no derivative of $g$ is assumed.

Suppose $u$ is jointly continuous on the closed strip, has $C^2$ spatial slices
and actual ordinary time derivative at $0<t<T$, has uniform exponential spatial
growth on the closed strip, and satisfies

$$
u_t=\nu\partial_x^2u+qu\quad(0<t<T),\qquad u(0,x)=g(x).
$$

Then $u(t,x)=\Phi_{\nu,q,g}(t,x)$ for all $0\le t\le T$ and all $x$, where
$\Phi$ is the actual Volterra-series construction. This identifies classical
solutions without assuming their mild representation. The constructed field's
continuity, growth, positive-time spatial regularity and actual time equation
supply the comparison hypotheses. No terminal derivative, sign condition, or
initial smoothness is added.

## Sources

The maximum-principle background is Stanford Math 220B, [*Heat Equation*](https://web.stanford.edu/class/math220b/handouts/heateqn.pdf), Theorems 18 and 20, and James Nolen, [*Partial Differential Equations and Diffusion Processes*](https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf), §2.8. The exponential spatial barrier and exponential time factor derive the stated whole-line potential results; these references are not asserted to state exactly this linear-exponential growth class and endpoint formulation.
