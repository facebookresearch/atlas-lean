# Spatial smoothing for continuous forcing

Let $\nu>0$ and let $f:[0,T]\times\mathbb R\to\mathbb R$ be jointly continuous,
with constants $M,c\ge0$ satisfying $|f(s,x)|\le M e^{c|x|}$ uniformly on the strip.
Write $D_\nu f(t,x)=\int_0^t P_{\nu(t-s)}(f(s,\cdot))(x)\,ds$.
No spatial or time derivative of $f$ is assumed.
Let $P_t f$ be the whole-line Gaussian heat evolution and
$K_1(y)=(4\pi)^{-1/2}e^{-y^2/4}$ its time-one kernel.

For every $0\le t\le T$ and $x\in\mathbb R$, the actual spatial derivative exists and equals
$$
\partial_xD_\nu f(t,x)=-\frac{\sqrt t}{\sqrt\nu}
\int_0^1\int_{\mathbb R}yK_1(y)
 f\bigl(t(1-r^2),x-\sqrt{\nu t}\,r y\bigr)\,dy\,dr.
$$
The time substitution supplies a factor $r$ that cancels the heat-gradient
singularity. Gaussian first-moment domination gives a bound uniform in a spatial
neighborhood, justifying differentiation. Positive heat times suffice almost
everywhere in $r$; $t=0$ is proved separately from the zero Duhamel field.
This does not assert a classical heat PDE from merely continuous forcing.

## Sources

James Nolen, [*Partial Differential Equations and Diffusion Processes*](https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf), §2.3, pp. 16–17 (Gaussian differentiation), and §2.4, formula (4.42) (Duhamel construction). The explicit exponential-weight estimates and the continuous-forcing first-derivative conclusion are justified in the linked Lean proofs; the classical PDE theorem in the notes has stronger forcing regularity.
