# One Langevin Monte Carlo step from a point is Gaussian

Let $E$ be a finite-dimensional real inner product space, $f : E \to \mathbb{R}$ with continuous gradient, $h \in \mathbb{R}$ and $x \in E$. Then

$$
\mathrm{LMC}_{f,h}(\delta_x) = \mathcal N(0, I) \circ \bigl(\xi \mapsto x - h\nabla f(x) + \sqrt{2h}\,\xi\bigr)^{-1},
$$

which for $h \ge 0$ is the Gaussian law $\mathcal N(x - h\nabla f(x),\, 2h\, I)$: the transition kernel of the algorithm is a gradient-descent step followed by Gaussian noise of variance $2h$.

## Background

- [One step of the Langevin Monte Carlo algorithm, on laws](lmc-step.md): the definition, evaluated at a Dirac mass.

## Sources

- A. S. Dalalyan, *Further and stronger analogy between sampling and optimization: Langevin Monte Carlo and gradient descent*, arXiv:1704.04752v2 (COLT 2017), update rule (2) with a deterministic starting point.
