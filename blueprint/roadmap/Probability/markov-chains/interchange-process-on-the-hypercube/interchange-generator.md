# Generator of the interchange process on the hypercube

Let $n \in \mathbb{N}$, let $Q_n$ be the hypercube graph on $\{0, 1\}^n$ (two vertices adjacent when they differ in exactly one coordinate) with edge set $E$, and let $S$ be the group of permutations of $\{0, 1\}^n$. The generator of the unit-rate interchange process on $Q_n$ is the $S \times S$ matrix

$$L(\sigma, \tau) = \#\{\{x, y\} \in E : \tau = \sigma \circ (x\ y)\} - \mathbf{1}[\tau = \sigma]\, |E|,$$

where $(x\ y)$ is the transposition of $x$ and $y$. So $L(\sigma, \sigma \circ (x\ y)) = 1$ for each edge $\{x, y\}$, $L(\sigma, \sigma) = -|E|$, and all other entries are $0$: from $\sigma$ the process jumps at rate $1$ across each edge, exchanging the particles at its endpoints.
