# Derivative growth away from initial time

Let $P_t$ be whole-line Gaussian heat evolution, extended by $P_tg=g$ for
$t\le0$. Set $D_\nu f(t,x)=\int_0^t P_{\nu(t-s)}(f(s,\cdot))(x)\,ds$.
Write $\Phi_{\nu,q,g}$ for the actual Volterra field obtained by summing
$v_0(t,x)=P_{\nu t}g(x)$ and $v_{n+1}=D_\nu(qv_n)$; abbreviate it by $\Phi$.
Assume $q$ is jointly continuous on $[0,T]\times\mathbb R$ and
$|q(t,x)|\le Q$ there for a constant $Q\ge0$. Let $g$ be continuous with
$|g(x)|\le M e^{c|x|}$ for some $M,c\ge0$. No derivative of $q$ is assumed.

Let $\nu>0$ and $0<a\le T$. There are constants $A,b\ge0$ such that

$$
|\partial_x\Phi(a+s,x)|\le A e^{b|x|}
\qquad(0\le s\le T-a,\ x\in\mathbb R).
$$

Thus the actual spatial derivative has uniform exponential growth on $[a,T]$.
The free heat-gradient bound uses the positive lower denominator
$2\sqrt{\nu a}$; the Duhamel gradient is uniformly controlled on the original
closed strip. Different exponential rates may be combined. The case $a=T$
is included, but no bound at $a=0$ is asserted for arbitrary continuous $g$.

## Sources

James Nolen, [*Partial Differential Equations and Diffusion Processes*](https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf), §§2.3–2.4: Gaussian differentiation and Duhamel formula (4.42). Restart follows by splitting the Duhamel time integral and using the heat semigroup. The weighted first-derivative conclusions use Gaussian domination and the convergent Volterra construction, without the stronger classical-PDE hypotheses of Theorem 2.4.1.
