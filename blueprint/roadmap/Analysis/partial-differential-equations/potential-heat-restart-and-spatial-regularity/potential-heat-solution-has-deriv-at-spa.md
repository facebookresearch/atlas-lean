# First spatial derivative from continuous initial data

Let $P_t$ be whole-line Gaussian heat evolution, extended by $P_tg=g$ for
$t\le0$. Set $D_\nu f(t,x)=\int_0^t P_{\nu(t-s)}(f(s,\cdot))(x)\,ds$.
Write $\Phi_{\nu,q,g}$ for the actual Volterra field obtained by summing
$v_0(t,x)=P_{\nu t}g(x)$ and $v_{n+1}=D_\nu(qv_n)$; abbreviate it by $\Phi$.
Assume $q$ is jointly continuous on $[0,T]\times\mathbb R$ and
$|q(t,x)|\le Q$ there for a constant $Q\ge0$. Let $g$ be continuous with
$|g(x)|\le M e^{c|x|}$ for some $M,c\ge0$. No derivative of $q$ is assumed.

Let $\nu>0$, $0<t\le T$, and $x\in\mathbb R$. The ordinary spatial derivative
of $\Phi(t,\cdot)$ exists at $x$ and equals

$$
\partial_x\Phi(t,x)=\partial_x P_{\nu t}g(x)+\partial_xD_\nu(q\Phi)(t,x).
$$

The free heat term smooths exponentially growing continuous data. The forcing
$q\Phi$ is jointly continuous with uniform exponential growth, so its Duhamel
integral gains one spatial derivative. This asserts neither a derivative at
initial time for arbitrary $g$ nor a classical PDE from continuous forcing.

## Sources

James Nolen, [*Partial Differential Equations and Diffusion Processes*](https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf), §§2.3–2.4: Gaussian differentiation and Duhamel formula (4.42). Restart follows by splitting the Duhamel time integral and using the heat semigroup. The weighted first-derivative conclusions use Gaussian domination and the convergent Volterra construction, without the stronger classical-PDE hypotheses of Theorem 2.4.1.
