# Volterra iterates for a potential

For real $\nu$, a potential $q:\mathbb R^2\to\mathbb R$, and initial data
$g:\mathbb R\to\mathbb R$, define the successive Volterra terms recursively.
Write $P_tg$ for whole-line Gaussian heat evolution, with $P_tg=g$ for $t\le0$, and

$$
D_\nu f(t,x)=\int_0^t P_{\nu(t-s)}(f(s,\cdot))(x)\,ds.
$$

Set $v_0(t,x)=P_{\nu t}g(x)$, $v_{n+1}=D_\nu(qv_n)$, and
$\Phi(t,x)=\sum_{n=0}^\infty v_n(t,x)$.

The recursion defining $v_n$ requires no regularity assumptions. Each integral is a
Lebesgue integral with its usual totalized convention. Convergence and regularity
are separate conclusions under bounded-potential and exponential-growth hypotheses.

## Sources

James Nolen, [*Partial Differential Equations and Diffusion Processes*](https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf), §2.4, formula (4.42), for the Gaussian Duhamel representation. The weighted series estimates and mild uniqueness here follow by domination, iteration and the exponential series; they do not invoke the stronger classical-regularity conclusion of Theorem 2.4.1.
