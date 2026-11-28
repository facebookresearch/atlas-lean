# Brenier's theorem

Let $\mu$ and $\nu$ be probability measures on $\mathbb{R}^n$ with finite second moments, and suppose
that $\mu$ is absolutely continuous with respect to Lebesgue measure. For the quadratic cost
$|x - y|^2$ there is a measurable map $T : \mathbb{R}^n \to \mathbb{R}^n$ such that the coupling
$(\mathrm{id}, T)_\# \mu$ of $\mu$ and $\nu$ is optimal, every optimal coupling equals it, and
$T$ is $\mu$-almost everywhere the gradient of a convex function: there are an open convex set
$U$ of full $\mu$-measure and a function $\psi$ convex on $U$ with $T = \nabla \psi$ $\mu$-almost
everywhere.

## Idea

Monge asked for the cheapest way to move one distribution of mass onto another by a map. In
general no optimal map exists, which is why Kantorovich relaxed the problem to couplings; for the
quadratic cost and a starting measure with a density, Brenier's theorem says that the optimal
coupling is unique and is given by a map, the gradient of a convex function. On the line this is
the monotone rearrangement of one distribution onto the other. The proof uses that optimal
couplings are concentrated on cyclically monotone sets, which by Rockafellar's theorem lie in the
graph of the subdifferential of a convex function; a convex function is differentiable almost
everywhere, so for absolutely continuous $\mu$ the subdifferential is a gradient $\mu$-almost
everywhere.

## Statements

- [Brenier's theorem](brenier.md)
- [One-third stability of Brenier maps](one-third-stability-of-brenier-maps.md)
- [Three-atom sharpness of one-third Brenier stability](sharpness-of-one-third-brenier-stability.md)

## Sources

- C. Villani, *Optimal Transport: Old and New*, Grundlehren der mathematischen Wissenschaften 338, Springer, 2009, Chapter 9.
