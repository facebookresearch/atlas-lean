# Joint smoothness of every actual spatial derivative

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

For every $k\in\mathbb N$, the field $(t,x)\mapsto J_k\Phi(t,x)$ is jointly
$C^\infty$ on $(0,T)\times\mathbb R$.

Spatial potential jets are evaluations of $D^jQ$ on copies of the unit vector
$(0,1)$, so they are smooth and inherit the required strip bounds. A simultaneous
induction on joint regularity order, quantified over all spatial jet orders,
uses the proved time evolution of each jet and its actual next spatial
derivative. The continuous-partials theorem supplies the joint derivative;
the finite Leibniz formula supplies regularity of the differentiated forcing.
Neither initial-data smoothness nor an assumed interchange of mixed derivatives
is used. The domain is empty if $T\le0$.

## Sources

James Nolen, [*Partial Differential Equations and Diffusion Processes*](https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf), §§2.3–2.4, especially Duhamel formula (4.42), supplies the classical heat-kernel and differentiation background. The exponential-growth restart and simultaneous spatial-jet arguments here derive the stated conclusions from the proved estimates; the reference is not a statement of these exact weighted hypotheses. The formal joint-differentiability step uses Mathlib's theorem combining continuous partial derivatives and its finite-order Fréchet derivative characterizations.
