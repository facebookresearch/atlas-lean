# Classical equation for bounded smooth potentials

Let $\Phi=\Phi_{\nu,q,g}$ denote the actual potential-heat Volterra
construction with viscosity $\nu>0$, potential $q$, and initial datum $g$.
Write $J_k\Phi(t,x)=\partial_x^k\Phi(t,x)$ and
$J_k(q\Phi)(t,x)=\partial_x^k(q(t,x)\Phi(t,x))$ for actual iterated
ordinary spatial derivatives. Assume $g$ is continuous and
$|g(x)|\le A e^{c|x|}$ for constants $A,c\ge0$.

Assume $Q(t,x)=q(t,x)$ is jointly $C^\infty$ on $\mathbb R^2$.
For every natural $j$, assume there is a finite constant $M_j$ such that

$$
\|D^j Q(t,x)\|\le M_j\qquad(0\le t\le T,\ x\in\mathbb R).
$$

Here $D^jQ$ is the actual iterated Fréchet derivative, with its multilinear
operator norm. Each order may have a separate bound; order zero includes
boundedness of the potential. No analyticity, separability, or uniform bound
across all derivative orders is required.

For $0<t<T$ and every real $x$, the constructed solution has the actual time derivative

$$
\frac{d}{dt}\Phi(t,x)=\nu\partial_x^2\Phi(t,x)+q(t,x)\Phi(t,x).
$$

The smooth-potential Fréchet hypotheses imply the finite spatial derivative
bounds needed for the classical equation. This supplies the PDE directly under
the same potential assumptions as the joint-smoothness theorem. The initial
datum remains merely continuous with exponential growth.

## Sources

James Nolen, [*Partial Differential Equations and Diffusion Processes*](https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf), §§2.3–2.4, especially Duhamel formula (4.42), supplies the classical heat-kernel and differentiation background. The exponential-growth restart and simultaneous spatial-jet arguments here derive the stated conclusions from the proved estimates; the reference is not a statement of these exact weighted hypotheses. The formal joint-differentiability step uses Mathlib's theorem combining continuous partial derivatives and its finite-order Fréchet derivative characterizations.
