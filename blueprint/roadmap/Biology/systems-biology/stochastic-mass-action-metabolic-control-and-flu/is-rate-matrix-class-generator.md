# Restricted mass-action generator is a rate matrix

Let $N$ be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with finite species set $S$ and finite reaction set $\rho$, let $k_r \ge 0$ be rate constants and let $\Omega \subseteq \mathbb{N}^S$ be a finite set
such that $\Omega$ is closed under firing (if $x \in \Omega$ and $\mathrm{src}(r) \le x$, then $x - \mathrm{src}(r) + \mathrm{prod}(r) \in \Omega$). Then the [restricted generator](class-generator.md) $Q$ on $\Omega$ is a rate matrix: its off-diagonal
entries are nonnegative and its rows sum to $0$.
