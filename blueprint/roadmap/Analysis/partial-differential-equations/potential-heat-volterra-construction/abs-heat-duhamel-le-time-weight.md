# Duhamel bound with a time-dependent amplitude

Let $\nu,c\ge0$, $0\le t\le T$, and let $f$ be jointly continuous on
$[0,T]\times\mathbb R$. Let $a:\mathbb R\to\mathbb R$ be nonnegative on $[0,T]$
and integrable on the interval from $0$ to $t$. Suppose
$|f(s,x)|\le a(s)e^{c|x|}$ for every $s\in[0,T]$ and real $x$.
Write $D_\nu f(t,x)=\int_0^t P_{\nu(t-s)}f(s,\cdot)(x)\,ds$ and
$J=\int_{\mathbb R}K_1(y)e^{c\sqrt{\nu T}|y|}\,dy$, where
$K_1(y)=(4\pi)^{-1/2}e^{-y^2/4}$. Then

$$
|D_\nu f(t,x)|\le\left(\int_0^t a(s)\,ds\right)J e^{c|x|}.
$$

No continuity of the amplitude $a$ is required.

## Sources

James Nolen, [*Partial Differential Equations and Diffusion Processes*](https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf), §2.4, formula (4.42), for the Gaussian Duhamel representation. The weighted series estimates and mild uniqueness here follow by domination, iteration and the exponential series; they do not invoke the stronger classical-regularity conclusion of Theorem 2.4.1.
