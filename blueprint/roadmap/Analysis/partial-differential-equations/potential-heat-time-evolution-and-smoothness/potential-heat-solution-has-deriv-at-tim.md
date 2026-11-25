# Classical potential-heat equation under finite spatial regularity

Let $\Phi=\Phi_{\nu,q,g}$ denote the actual potential-heat Volterra
construction with viscosity $\nu>0$, potential $q$, and initial datum $g$.
Write $J_k\Phi(t,x)=\partial_x^k\Phi(t,x)$ and
$J_k(q\Phi)(t,x)=\partial_x^k(q(t,x)\Phi(t,x))$ for actual iterated
ordinary spatial derivatives. Assume $g$ is continuous and
$|g(x)|\le A e^{c|x|}$ for constants $A,c\ge0$.

For each time $s\in[0,T]$, assume $q(s,\cdot)\in C^{2}(\mathbb R)$.
For every $0\le j\le 2$, assume $J_jq$ is jointly continuous on
$[0,T]\times\mathbb R$ and there is a finite constant $M_j$ such that
$|J_jq(s,x)|\le M_j$ throughout this strip. The constants may depend on $j$.
No potential time derivative or initial-data derivative is assumed.

For $0<t<T$ and every real $x$, the ordinary time derivative exists and satisfies

$$
\frac{d}{dt}\Phi(t,x)=\nu\partial_x^2\Phi(t,x)+q(t,x)\Phi(t,x).
$$

The second spatial derivative is the actual twice-iterated ordinary derivative.
This is the order-zero spatial-jet evolution identity, applied to the constructed
field. Potentials with time cusps are allowed under the stated spatial and joint
continuity assumptions; no ordinary time derivative at either endpoint is claimed.

## Sources

James Nolen, [*Partial Differential Equations and Diffusion Processes*](https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf), §§2.3–2.4, especially Duhamel formula (4.42), supplies the classical heat-kernel and differentiation background. The exponential-growth restart and simultaneous spatial-jet arguments here derive the stated conclusions from the proved estimates; the reference is not a statement of these exact weighted hypotheses. The formal joint-differentiability step uses Mathlib's theorem combining continuous partial derivatives and its finite-order Fréchet derivative characterizations.
