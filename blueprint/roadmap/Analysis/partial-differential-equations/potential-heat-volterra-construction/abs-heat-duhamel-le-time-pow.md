# Polynomial time envelopes gain a degree

Let $\nu,A,c\ge0$, $0\le t\le T$, and $n\ge0$ an integer. Let $f$ be jointly
continuous on $[0,T]\times\mathbb R$ and satisfy
$|f(s,x)|\le A s^n e^{c|x|}$ on that strip.
Write $D_\nu f(t,x)=\int_0^t P_{\nu(t-s)}f(s,\cdot)(x)\,ds$ and
$J=\int_{\mathbb R}K_1(y)e^{c\sqrt{\nu T}|y|}\,dy$, with
$K_1(y)=(4\pi)^{-1/2}e^{-y^2/4}$. Then

$$
|D_\nu f(t,x)|\le\frac{A t^{n+1}}{n+1}J e^{c|x|}.
$$

Integrating the amplitude $As^n$ supplies the factorial step used in Volterra iteration.

## Sources

James Nolen, [*Partial Differential Equations and Diffusion Processes*](https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf), §2.4, formula (4.42), for the Gaussian Duhamel representation. The weighted series estimates and mild uniqueness here follow by domination, iteration and the exponential series; they do not invoke the stronger classical-regularity conclusion of Theorem 2.4.1.
