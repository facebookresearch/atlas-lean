# Stationary law of the stochastic mass-action chain on a finite class

Let $N$ be a [chemical reaction network](../complex-balancing-and-the-deficiency-zero-theore/reaction-network.md) with finite species set $S$ and finite reaction set $\rho$, let $k_r \ge 0$ be rate constants and let $c \in \mathbb{R}_{>0}^S$ be [complex balanced](../complex-balancing-and-the-deficiency-zero-theore/is-complex-balanced.md)
for $k$. Let $\Omega \subseteq \mathbb{N}^S$ be a finite nonempty set of states such that $\Omega$ is closed under firing (if $x \in \Omega$ and $\mathrm{src}(r) \le x$, then $x - \mathrm{src}(r) + \mathrm{prod}(r) \in \Omega$)
and $\Omega$ is closed under reverse firing (if $x \in \Omega$ and $\mathrm{prod}(r) \le x$, then $x - \mathrm{prod}(r) + \mathrm{src}(r) \in \Omega$). Then the [restricted generator](class-generator.md) $Q$ on $\Omega$ is a rate matrix, and the
[normalized Poisson law](class-stationary-law.md) $\pi_\Omega(x) \propto \prod_s c_s^{x_s} e^{-c_s}/x_s!$
on $\Omega$ is a probability vector with $\pi_\Omega(x) > 0$ for every $x \in \Omega$ that is
invariant under the transition semigroup: $\pi_\Omega e^{tQ} = \pi_\Omega$ for every real $t$
(Anderson, Craciun & Kurtz 2010, Thm 4.1–4.2).
