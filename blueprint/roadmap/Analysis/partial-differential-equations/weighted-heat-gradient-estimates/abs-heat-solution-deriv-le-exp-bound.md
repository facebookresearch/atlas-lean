# Weighted heat-gradient estimate

Let $P_t f$ be the whole-line Gaussian heat evolution and
$K_1(y)=(4\pi)^{-1/2}e^{-y^2/4}$ its time-one kernel.

Let $f$ be continuous with $|f(y)|\le M e^{c|y|}$, where $M,c\ge0$.
For $0<t\le H$,
$$
|\partial_x P_t f(x)|\le \frac{M}{2\sqrt t}
\left(\int_{\mathbb R}|y|K_1(y)e^{c\sqrt H|y|}\,dy\right)e^{c|x|}.
$$
The Gaussian moment is finite. The proof combines the actual rescaled derivative
formula with the affine first-moment bound. No derivative of $f$ is required;
no assertion at heat time zero is made.

## Sources

James Nolen, [*Partial Differential Equations and Diffusion Processes*](https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf), §2.3, pp. 16–17 (Gaussian differentiation), and §2.4, formula (4.42) (Duhamel construction). The explicit exponential-weight estimates and the continuous-forcing first-derivative conclusion are justified in the linked Lean proofs; the classical PDE theorem in the notes has stronger forcing regularity.
