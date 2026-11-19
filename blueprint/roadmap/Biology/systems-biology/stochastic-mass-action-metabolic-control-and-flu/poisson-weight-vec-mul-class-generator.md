# Anderson–Craciun–Kurtz on a finite class

Let $N$ be a [chemical reaction network](../complex-balancing-and-the-deficiency-zero-theore/reaction-network.md) with finite species set $S$ and finite reaction set $\rho$, let $k \in \mathbb{R}^\rho$ and $c \in \mathbb{R}^S$ with $c$ [complex balanced](../complex-balancing-and-the-deficiency-zero-theore/is-complex-balanced.md) for $k$, and let
$\Omega \subseteq \mathbb{N}^S$ be a finite set such that $\Omega$ is closed under reverse firing (if $x \in \Omega$ and $\mathrm{prod}(r) \le x$, then $x - \mathrm{prod}(r) + \mathrm{src}(r) \in \Omega$). Then the
[Poisson weights](poisson-weight.md) $\pi(x) = \prod_s c_s^{x_s} e^{-c_s}/x_s!$, restricted to $\Omega$, are invariant for the [restricted generator](class-generator.md) $Q$: $\pi Q = 0$
(Anderson, Craciun & Kurtz 2010, Thm 4.1–4.2). For instance, the closure condition holds when
$\Omega$ is a finite closed communicating class of a weakly reversible network with positive rate
constants, since a reaction path from the product back to the source leads from $x$ to the state
before the firing.
