# Summing under the Duhamel integral

Let $I$ be countable, $\nu,c\ge0$, and $0\le t\le T$. For each $i\in I$, let
$f_i$ be jointly continuous on $[0,T]\times\mathbb R$. Suppose $(A_i)$ is a
summable family of nonnegative reals and
$|f_i(s,y)|\le A_i e^{c|y|}$ for every $i$, $s\in[0,T]$, and real $y$.
Write $D_\nu f(t,x)=\int_0^t P_{\nu(t-s)}(f(s,\cdot))(x)\,ds$.
Then for every real $x$,

$$
\sum_{i\in I}D_\nu f_i(t,x)=D_\nu\left(\sum_{i\in I}f_i\right)(t,x),
$$

with convergence of the left-hand series. A fixed Gaussian exponential moment
provides a summable, time-independent majorant on the finite integration interval.
The conclusion includes $t=0$ and zero viscosity.

## Sources

James Nolen, [*Partial Differential Equations and Diffusion Processes*](https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf), §2.4, formula (4.42), for the Gaussian Duhamel representation. The weighted series estimates and mild uniqueness here follow by domination, iteration and the exponential series; they do not invoke the stronger classical-regularity conclusion of Theorem 2.4.1.
