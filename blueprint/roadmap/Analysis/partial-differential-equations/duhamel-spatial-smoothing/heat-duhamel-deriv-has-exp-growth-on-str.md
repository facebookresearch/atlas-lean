# Exponential growth of the smoothed derivative

Let $\nu>0$ and let $f:[0,T]\times\mathbb R\to\mathbb R$ be jointly continuous,
with constants $M,c\ge0$ satisfying $|f(s,x)|\le M e^{c|x|}$ uniformly on the strip.
Write $D_\nu f(t,x)=\int_0^t P_{\nu(t-s)}(f(s,\cdot))(x)\,ds$.
No spatial or time derivative of $f$ is assumed.

The actual derivative $(t,x)\mapsto\partial_xD_\nu f(t,x)$ has a uniform
exponential spatial bound on the same finite strip. One may use growth exponent
$c$ and coefficient
$$
\frac{M\sqrt T}{\sqrt\nu}
\int_{\mathbb R}|y|K_1(y)e^{c\sqrt{\nu T}|y|}\,dy.
$$
The proof bounds $\sqrt t$ by $\sqrt T$ in the quantitative estimate. The Lean
statement allows any real $T$; when $T<0$ the specified strip is empty. For
$T=0$ the derivative vanishes. There is no hypothesis on forcing derivatives.

## Sources

James Nolen, [*Partial Differential Equations and Diffusion Processes*](https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf), §2.3, pp. 16–17 (Gaussian differentiation), and §2.4, formula (4.42) (Duhamel construction). The explicit exponential-weight estimates and the continuous-forcing first-derivative conclusion are justified in the linked Lean proofs; the classical PDE theorem in the notes has stronger forcing regularity.
