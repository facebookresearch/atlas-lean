# Poisson summation formula in Euclidean space

Let $\iota$ be a finite index set, $f$ a complex-valued Schwartz function on the Euclidean space $\mathbb{R}^\iota$ and $x \in \mathbb{R}^\iota$. Then

$$\sum_{n \in \mathbb{Z}^\iota} f(x + n) = \sum_{n \in \mathbb{Z}^\iota} \hat f(n)\, e^{2\pi i \langle n, x\rangle},$$

where $\mathbb{Z}^\iota$ is the coordinate integer lattice. This is the multi-dimensional analogue of Mathlib's one-dimensional Poisson summation formula `SchwartzMap.tsum_eq_tsum_fourier`.
