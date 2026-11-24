# Integrability after affine rescaling

Let $P_t f$ be the whole-line Gaussian heat evolution and
$K_1(y)=(4\pi)^{-1/2}e^{-y^2/4}$ its time-one kernel.

Suppose $f:\mathbb R\to\mathbb R$ is continuous and
$|f(y)|\le M e^{c|y|}$ for some $M,c\ge0$. For arbitrary real $z,s$,

$$y\longmapsto yK_1(y)f(z-sy)$$

is Lebesgue integrable. This includes negative and zero scales. The proof
bounds the affine datum by an exponential in $|y|$ and uses the integrable
weighted first absolute Gaussian moment.

## Sources

James Nolen, [*Partial Differential Equations and Diffusion Processes*](https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf), §2.3, pp. 16–17 (Gaussian differentiation), and §2.4, formula (4.42) (Duhamel construction). The explicit exponential-weight estimates and the continuous-forcing first-derivative conclusion are justified in the linked Lean proofs; the classical PDE theorem in the notes has stronger forcing regularity.
