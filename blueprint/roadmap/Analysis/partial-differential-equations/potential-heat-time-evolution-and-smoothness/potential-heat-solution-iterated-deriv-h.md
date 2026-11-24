# Actual time evolution of spatial potential-heat derivatives

Let $\Phi=\Phi_{\nu,q,g}$ denote the actual potential-heat Volterra
construction with viscosity $\nu>0$, potential $q$, and initial datum $g$.
Write $J_k\Phi(t,x)=\partial_x^k\Phi(t,x)$ and
$J_k(q\Phi)(t,x)=\partial_x^k(q(t,x)\Phi(t,x))$ for actual iterated
ordinary spatial derivatives. Assume $g$ is continuous and
$|g(x)|\le A e^{c|x|}$ for constants $A,c\ge0$.

For each time $s\in[0,T]$, assume $q(s,\cdot)\in C^{n+2}(\mathbb R)$.
For every $0\le j\le n+2$, assume $J_jq$ is jointly continuous on
$[0,T]\times\mathbb R$ and there is a finite constant $M_j$ such that
$|J_jq(s,x)|\le M_j$ throughout this strip. The constants may depend on $j$.
No potential time derivative or initial-data derivative is assumed.

Fix $n\in\mathbb N$. For $0<t<T$ and every real $x$, the ordinary time
derivative of $J_n\Phi(\cdot,x)$ exists and equals

$$
\frac{d}{dt}J_n\Phi(t,x)
 =\nu J_{n+2}\Phi(t,x)+J_n(q\Phi)(t,x).
$$

At a fixed target time, choose and then hold fixed an earlier restart time
$a=t/2$. Differentiate the already proved spatially differentiated restart
identity on a neighborhood of the target. Heat and Duhamel time formulas,
followed by the independent restart identity at order $n+2$, yield this
formula. No mixed-derivative commutation is presumed. Ordinary time
differentiability is asserted only at interior times.

## Sources

James Nolen, [*Partial Differential Equations and Diffusion Processes*](https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf), §§2.3–2.4, especially Duhamel formula (4.42), supplies the classical heat-kernel and differentiation background. The exponential-growth restart and simultaneous spatial-jet arguments here derive the stated conclusions from the proved estimates; the reference is not a statement of these exact weighted hypotheses. The formal joint-differentiability step uses Mathlib's theorem combining continuous partial derivatives and its finite-order Fréchet derivative characterizations.
