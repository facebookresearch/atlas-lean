# Factorial bounds for Volterra terms

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
For the chosen bounds $M,c,Q$, define the finite nonnegative Gaussian moment

$$
J=\int_{\mathbb R}K_1(y)e^{c\sqrt{\nu T}|y|}\,dy,
\qquad K_1(y)=(4\pi)^{-1/2}e^{-y^2/4}.
$$

For every integer $n\ge0$, $0\le t\le T$, and $x\in\mathbb R$,

$$
|v_n(t,x)|\le MJ\frac{(QJ)^n t^n}{n!}e^{c|x|}.
$$

Each time integration contributes one power of time and the next factorial divisor.
The moment $J$ is fixed at the horizon, independent of $n,t,x$.

## Sources

James Nolen, [*Partial Differential Equations and Diffusion Processes*](https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf), §2.4, formula (4.42), for the Gaussian Duhamel representation. The weighted series estimates and mild uniqueness here follow by domination, iteration and the exponential series; they do not invoke the stronger classical-regularity conclusion of Theorem 2.4.1.
