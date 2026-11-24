# Uniqueness among exponentially growing mild solutions

Write $P_tg$ for whole-line Gaussian heat evolution, with $P_tg=g$ for $t\le0$, and

$$
D_\nu f(t,x)=\int_0^t P_{\nu(t-s)}(f(s,\cdot))(x)\,ds.
$$

Set $v_0(t,x)=P_{\nu t}g(x)$, $v_{n+1}=D_\nu(qv_n)$, and
$\Phi(t,x)=\sum_{n=0}^\infty v_n(t,x)$.
Let $\nu\ge0$ and $T\in\mathbb R$. Assume $q$ is jointly continuous on
$[0,T]\times\mathbb R$ and $|q(t,x)|\le Q$ there for a constant $Q\ge0$.
Let $g:\mathbb R\to\mathbb R$ be continuous with exponential growth:
$|g(x)|\le M e^{c|x|}$ for some $M,c\ge0$.

Let $u$ be jointly continuous on $[0,T]\times\mathbb R$, with constants $A,b\ge0$
satisfying $|u(t,x)|\le A e^{b|x|}$ throughout that strip. Suppose, at every point
of the strip,

$$
u(t,x)=P_{\nu t}g(x)+D_\nu(qu)(t,x).
$$

Then $u(t,x)=\Phi(t,x)$ for every $0\le t\le T$ and $x\in\mathbb R$.
The competitor's growth exponent may differ from that of the initial data.
Iterating the homogeneous equation for $u-\Phi$ gives a factorial remainder
that tends to zero. No classical PDE or derivative bounds are assumed.

## Sources

James Nolen, [*Partial Differential Equations and Diffusion Processes*](https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf), §2.4, formula (4.42), for the Gaussian Duhamel representation. The weighted series estimates and mild uniqueness here follow by domination, iteration and the exponential series; they do not invoke the stronger classical-regularity conclusion of Theorem 2.4.1.
