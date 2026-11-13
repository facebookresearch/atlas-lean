# Continuous mapping theorem for weak convergence of probability measures

Let $\mu_n$
($n \in \mathbb{N}$) and $\mu$ be probability measures on $\mathbb{R}$, and let
$g : \mathbb{R} \to \mathbb{R}$ be a measurable function whose set of discontinuity points has
$\mu$-measure zero. If $\mu_n$ converges weakly to $\mu$ as $n \to \infty$, then the pushforward
probability measures $\mu_n \circ g^{-1}$ converge weakly to $\mu \circ g^{-1}$.

This generalizes the case where $g$ is continuous everywhere, which is already in Mathlib.

## Sources

- Lecture 12, continuous mapping theorem.
