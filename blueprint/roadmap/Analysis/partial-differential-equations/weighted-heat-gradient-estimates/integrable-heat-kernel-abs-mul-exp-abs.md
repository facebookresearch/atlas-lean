# Integrability of the weighted first Gaussian moment

For every $t>0$ and every real $c$, the function

$$y\longmapsto |y|K_t(y)e^{c|y|}$$

is Lebesgue integrable on $\mathbb R$. The proof rewrites the kernel explicitly
and applies Gaussian domination of polynomial times exponential growth with
polynomial degree one. The weight parameter need not be nonnegative.

## Sources

James Nolen, [*Partial Differential Equations and Diffusion Processes*](https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf), §2.3, pp. 16–17 (Gaussian differentiation), and §2.4, formula (4.42) (Duhamel construction). The explicit exponential-weight estimates and the continuous-forcing first-derivative conclusion are justified in the linked Lean proofs; the classical PDE theorem in the notes has stronger forcing regularity.
