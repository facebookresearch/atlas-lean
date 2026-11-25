# Differential entropy and Gaussian maximum entropy

Let $X$ be a real random variable with a density $f$, variance at most $P$ with $P > 0$, and differential entropy
$h(X) = -\int f \log f$ well defined in $[-\infty, \infty)$. Then $h(X) \le \tfrac12 \log(2\pi e P)$, with equality if and only if $X$
is Gaussian with variance $P$ (any mean). Under the second-moment constraint $\mathbb{E}[X^2] \le P$ instead, the same bound
holds, with equality if and only if $X \sim \mathcal{N}(0, P)$. The bound uses the logarithm base of $h$.

## Expansion

This node states a precise result. A good expansion adds a page for each pending prerequisite below and links it under
the dependency sections.

- Statement prerequisite: Differential entropy of a real random variable with a density, with values in $[-\infty, \infty)$.
- Proof prerequisite: Nonnegativity of the Kullback–Leibler divergence of probability measures, zero only for equal
  measures.

## Related topics

- [Differential entropy](../../Probability/high-dimensional-probability/isotropic-constant-of-log-concave-laws/differential-entropy.md)
- [Cross-entropy is entropy plus divergence](../entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/cross-entropy-eq-shannon-entropy-add-kl.md)

## Sources

- Y. Polyanskiy and Y. Wu, *Information Theory: From Coding to Learning*, Cambridge University Press, 2025 (author draft),
  Definition 2.6 and Theorem 2.8: (2.19) with $d = 1$, $\Sigma = P$ and (2.20) with $d = 1$, $a = P$; the equality cases
  follow from the divergence identity in its proof. <https://people.lids.mit.edu/yp/homepage/data/itbook-export.pdf>
