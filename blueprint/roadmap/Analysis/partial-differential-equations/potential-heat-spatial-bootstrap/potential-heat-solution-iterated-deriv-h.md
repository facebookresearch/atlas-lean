# Exponential growth of positive-time spatial derivatives

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

Let $0<a\le T$. There are constants $B,d\ge0$ such that

$$
|J_n\Phi(a+s,x)|\le B e^{d|x|}
\qquad(0\le s\le T-a,\ x\in\mathbb R).
$$

The constants may depend on the derivative order and positive lower endpoint.
This is a uniform bound on the whole closed strip $[a,T]$, expressed in elapsed
time after $a$. It includes $a=T$. The Gaussian gradient estimate uses a
strictly positive elapsed-time lower bound after restarting at $a/2$; no
bound uniform down to $a=0$ is asserted.

## Sources

James Nolen, [*Partial Differential Equations and Diffusion Processes*](https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf), §§2.3–2.4, especially Duhamel formula (4.42), gives the classical analytic starting points. The finite-order exponential-growth bootstrap here is derived from the proved Volterra restart and weighted heat/Duhamel derivative estimates; this reference is not a statement of these exact hypotheses.
