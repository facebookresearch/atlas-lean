# Weighted first-moment bound

Let $P_t f$ be the whole-line Gaussian heat evolution and
$K_1(y)=(4\pi)^{-1/2}e^{-y^2/4}$ its time-one kernel.

Let $f$ be continuous, $M,c\ge0$, and $|f(y)|\le M e^{c|y|}$ for all $y$.
If $s,S\in\mathbb R$ satisfy $|s|\le S$, then

$$
\left|\int_{\mathbb R}yK_1(y)f(x-sy)\,dy\right|
\le M e^{c|x|}\int_{\mathbb R}|y|K_1(y)e^{cS|y|}\,dy.
$$

All integrals are justified by Gaussian domination. The proof uses
$|x-sy|\le |x|+S|y|$, then the triangle inequality and monotonicity of integration.

## Sources

James Nolen, [*Partial Differential Equations and Diffusion Processes*](https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf), §2.3, pp. 16–17 (Gaussian differentiation), and §2.4, formula (4.42) (Duhamel construction). The explicit exponential-weight estimates and the continuous-forcing first-derivative conclusion are justified in the linked Lean proofs; the classical PDE theorem in the notes has stronger forcing regularity.
