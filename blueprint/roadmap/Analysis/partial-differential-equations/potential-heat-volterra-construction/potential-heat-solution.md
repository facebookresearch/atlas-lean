# Potential-heat Volterra field

Write $P_tg$ for whole-line Gaussian heat evolution, with $P_tg=g$ for $t\le0$, and

$$
D_\nu f(t,x)=\int_0^t P_{\nu(t-s)}(f(s,\cdot))(x)\,ds.
$$

Set $v_0(t,x)=P_{\nu t}g(x)$, $v_{n+1}=D_\nu(qv_n)$, and
$\Phi(t,x)=\sum_{n=0}^\infty v_n(t,x)$.

For arbitrary real $\nu$ and real-valued $q,g$, this defines the pointwise Volterra
field. The infinite sum is totalized (zero when not summable). For nonnegative
viscosity, a bounded jointly continuous potential on
$[0,T]\times\mathbb R$, and continuous exponentially growing initial data,
absolute convergence at $0\le t\le T$ is a separate theorem.
The definition alone asserts no PDE.

## Sources

James Nolen, [*Partial Differential Equations and Diffusion Processes*](https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf), §2.4, formula (4.42), for the Gaussian Duhamel representation. The weighted series estimates and mild uniqueness here follow by domination, iteration and the exponential series; they do not invoke the stronger classical-regularity conclusion of Theorem 2.4.1.
