# Density of the multivariate normal distribution

Let $\iota$ be a finite set with $n$ elements, $\mu \in \mathbb{R}^\iota$, and $S$ a positive definite real $\iota \times \iota$ matrix. The multivariate normal law $N(\mu, S)$ on the Euclidean space $\mathbb{R}^\iota$, the image of the standard Gaussian measure under $x \mapsto \mu + S^{1/2} x$, has density $x \mapsto (2\pi)^{-n/2} (\det S)^{-1/2} \exp\bigl(-\tfrac12 (x - \mu)^\top S^{-1} (x - \mu)\bigr)$ with respect to Lebesgue measure.

## Idea

Defining $N(\mu, S)$ as an affine image of the standard Gaussian works for every positive semidefinite $S$. A density exists only when $S$ is positive definite; otherwise the law sits on a proper affine subspace, which has Lebesgue measure zero. The proof is a change of variables. The standard Gaussian on $\mathbb{R}^n$ has density $(2\pi)^{-n/2} e^{-\|v\|^2/2}$, the product of $n$ one-dimensional normal densities. Pushing a density forward along the invertible affine map $v \mapsto \mu + S^{1/2} v$ divides it by the Jacobian $\det S^{1/2} = \sqrt{\det S}$ and evaluates it at $v = S^{-1/2}(x - \mu)$. Then $\|S^{-1/2}(x - \mu)\|^2 = (x - \mu)^\top S^{-1} (x - \mu)$ gives the quadratic form in the exponent.

## Statements

- [The multivariate Gaussian density](multivariate-gaussian-eq-with-density.md)
- [Multivariate Gaussian density function](multivariate-gaussian-pdfreal.md): definition used in the main statement
- [Standard Gaussian density function](std-gaussian-pdfreal.md): definition used in the proof of the main statement
- [Standard Gaussian measure via its density](std-gaussian-density-measure.md): definition used in the proof of the main statement
- [The standard Gaussian has a density](std-gaussian-eq-with-density.md): special case: the standard Gaussian
- [The affine change of variables as a measurable equivalence](affine-equiv.md): definition used in the proof of the main statement
- [Lebesgue measure under an invertible affine map](map-affine-equiv-volume.md): lemma used in the proof of the main statement
- [Pushforward of a measure with density](map-with-density-measurable-equiv.md): lemma used in the proof of the main statement
- [Quadratic form of the inverse square root](norm-sq-sqrt-inv-apply.md): lemma used in the proof of the main statement
