# Continuity of spatial derivatives throughout positive time

Let $P_t$ denote whole-line Gaussian heat evolution and
$D_\nu f(t,x)=\int_0^t P_{\nu(t-s)}(f(s,\cdot))(x)\,ds$.
Let $\Phi=\Phi_{\nu,q,g}$ be the actual potential-heat Volterra construction,
with initial datum $g$ and potential $q$. Write $J_k\Phi(t,x)$ and
$J_kq(t,x)$ for their actual iterated ordinary spatial derivatives.
Fix $n\in\mathbb N$ and $\nu>0$. Assume each potential slice
$q(s,\cdot)$ is $C^n$ for $s\in[0,T]$. For every $0\le k\le n$, assume
$J_kq$ is jointly continuous on $[0,T]\times\mathbb R$ and there is a finite
constant $M_k$ such that

$$
|J_kq(s,x)|\le M_k\qquad(0\le s\le T,\ x\in\mathbb R).
$$

The bounds may depend on $k$. Let $g$ be continuous, with
$|g(x)|\le A e^{c|x|}$ for some $A,c\ge0$. No spatial derivative of $g$
and no time derivative of $q$ is assumed.

The actual derivative field $(t,x)\mapsto J_n\Phi(t,x)$ is jointly continuous
on $(0,T]\times\mathbb R$.

For each point with positive time coordinate $t$, a closed strip starting at
$t/2$ supplies continuity on a relative neighborhood. This extends the closed-strip
result to the entire positive-time strip while retaining its terminal endpoint.
No initial-time derivative is claimed. If $T\le0$, the stated domain is empty.

## Sources

James Nolen, [*Partial Differential Equations and Diffusion Processes*](https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf), §§2.3–2.4, especially Duhamel formula (4.42), gives the classical analytic starting points. The finite-order exponential-growth bootstrap here is derived from the proved Volterra restart and weighted heat/Duhamel derivative estimates; this reference is not a statement of these exact hypotheses.
