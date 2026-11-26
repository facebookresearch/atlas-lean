# Infinite Blaschke products with finite fibers arbitrarily close to zero

This settles [Stephenson's question on fibers of infinite Blaschke products](blaschke-fibers-infinite-near-zero.md) in the negative: its statement is false.

Hayman and Lingham's Update 5.66 reports that Stephenson constructed an inner function $f$ such that the fiber $f^{-1}(w)$ is finite for a dense set of $w$ with $|w| < 1$, and that its Frostman shifts $f_\alpha = (f - \alpha)/(1 - \bar\alpha f)$ are Blaschke products for almost all $\alpha$. A fiber of $f_\alpha$ is a fiber of $f$ over a Möbius image of the point, so $f_\alpha$ also has finite fibers over a dense set, and in particular over points of every disc $|w| < \delta$.

For $f_\alpha$ to refute the linked statement it must also be an infinite Blaschke product, that is, have infinitely many zeros. Finite fibers on a dense set do not show this: $f(z) = z$ has all fibers finite and is a finite Blaschke product. What is needed is that Stephenson's $f$ is not a finite Blaschke product; the update does not say so explicitly, but it is implicit in its calling the question answered. Since Möbius maps of the disc take finite Blaschke products to finite Blaschke products, $f_\alpha$ is then not a finite Blaschke product either, so it has infinitely many zeros.

The update describes Stephenson's construction as unpublished: the resolution rests on this report in the published problem book, not on a published proof.

## Sources

- W. K. Hayman and E. F. Lingham, Research Problems in Function Theory, Fiftieth Anniversary Edition (2019), arXiv:1809.07200, Problem 5.66 (K. Stephenson); resolution: W. K. Hayman and E. F. Lingham, Research Problems in Function Theory, Fiftieth Anniversary Edition (2019), arXiv:1809.07200, Update 5.66 (K. Stephenson, unpublished), Update 5.66: 'Stephenson (unpublished) has answered this question negatively by constructing an inner function f such that f^\{-1\}(w) is finite on a dense subset of |w| < 1. Then f_α = (f − α)/(1 − ᾱ f) is a Blaschke product for almost all α', https://arxiv.org/abs/1809.07200.
