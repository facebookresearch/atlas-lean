# Quantitative bound for the Duhamel spatial derivative

Let $\nu>0$ and let $f:[0,T]\times\mathbb R\to\mathbb R$ be jointly continuous,
with constants $M,c\ge0$ satisfying $|f(s,x)|\le M e^{c|x|}$ uniformly on the strip.
Write $D_\nu f(t,x)=\int_0^t P_{\nu(t-s)}(f(s,\cdot))(x)\,ds$.
No spatial or time derivative of $f$ is assumed.
Let $P_t f$ be the whole-line Gaussian heat evolution and
$K_1(y)=(4\pi)^{-1/2}e^{-y^2/4}$ its time-one kernel.

For $0\le t\le T$ and every real $x$,

$$
|\partial_xD_\nu f(t,x)|\le
\frac{M\sqrt t}{\sqrt\nu}
\left(\int_{\mathbb R}|y|K_1(y)e^{c\sqrt{\nu T}|y|}\,dy\right)e^{c|x|}.
$$

The finite Gaussian moment is uniform over the strip. Apply the affine
first-moment estimate inside the fixed-time representation, use
$0\le r\le1$ and $t\le T$, and integrate the bound over an interval of length one.
The right side vanishes at initial time.

## Sources

James Nolen, [*Partial Differential Equations and Diffusion Processes*](https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf), §2.3, pp. 16–17 (Gaussian differentiation), and §2.4, formula (4.42) (Duhamel construction). The explicit exponential-weight estimates and the continuous-forcing first-derivative conclusion are justified in the linked Lean proofs; the classical PDE theorem in the notes has stronger forcing regularity.
