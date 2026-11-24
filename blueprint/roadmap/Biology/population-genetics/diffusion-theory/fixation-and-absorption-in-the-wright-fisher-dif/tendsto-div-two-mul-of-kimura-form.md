# Haldane's 2s in the joint regime, closed-form version

Let $u$ be a real function of two real variables with
$u(\sigma, x) = (1 - e^{-2\sigma x})/(1 - e^{-2\sigma})$ whenever $\sigma \ne 0$, for instance
[Kimura's fixation probability](../wright-fisher-diffusion/kimura-fixation.md). Let $(s_M)_{M \in \mathbb{N}}$ be real numbers with
$s_M \to 0$ and $M s_M \to \infty$. Then

$$\frac{u(M s_M, 1/M)}{2 s_M} \to 1 \quad (M \to \infty).$$

With $M$ gene copies, $1/M$ is the frequency of a single new copy and $M s_M$ the scaled selection
coefficient: the fixation probability of a new mutant is $2 s_M (1 + o(1))$, Haldane's
approximation.
