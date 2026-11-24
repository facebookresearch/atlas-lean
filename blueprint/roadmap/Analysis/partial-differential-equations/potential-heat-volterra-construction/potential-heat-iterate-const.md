# Constant-potential Volterra coefficients

Write $P_tg$ for whole-line Gaussian heat evolution, with $P_tg=g$ for $t\le0$, and

$$
D_\nu f(t,x)=\int_0^t P_{\nu(t-s)}(f(s,\cdot))(x)\,ds.
$$

Set $v_0(t,x)=P_{\nu t}g(x)$, $v_{n+1}=D_\nu(qv_n)$, and
$\Phi(t,x)=\sum_{n=0}^\infty v_n(t,x)$.

For constants $q(t,x)=b$ and $g(x)=a$, for all real $\nu,a,b,t,x$ and integers $n\ge0$,

$$
v_n(t,x)=a\frac{b^n t^n}{n!}.
$$

The time integral is oriented, so the identity also holds at negative times.
Spatially constant data are fixed by heat evolution at every real parameter.

## Sources

James Nolen, [*Partial Differential Equations and Diffusion Processes*](https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf), §2.4, formula (4.42), for the Gaussian Duhamel representation. The weighted series estimates and mild uniqueness here follow by domination, iteration and the exponential series; they do not invoke the stronger classical-regularity conclusion of Theorem 2.4.1.
