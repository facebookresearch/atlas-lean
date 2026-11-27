# I-projections

Let $Q$ be a distribution on a finite alphabet and $\Gamma$ a set of distributions. A minimiser
$P^*$ of the I-divergence $D(P \| Q) = \sum_a P(a)\log(P(a)/Q(a))$ over $\Gamma$ is the
*I-projection* of $Q$ on $\Gamma$ (Csiszár, "I-divergence geometry of probability distributions and
minimization problems", Ann. Probab. 3 (1975)). The divergence behaves like a squared Euclidean
distance: on a convex $\Gamma$ the I-projection satisfies the Pythagorean inequality
$D(P\|Q) \ge D(P\|P^*) + D(P^*\|Q)$, with equality on linear families and, more generally, when
$P^*$ is an algebraic inner point of $\Gamma$. Here $Q$ is strictly positive, distributions are
nonnegative functions summing to $1$, and logarithms are natural.

- [Existence of the I-projection on a closed set](existence-of-the-i-projection.md)
- [I-projection: support and Pythagorean inequality](pythagorean-inequality-for-i-projections.md)
- [First-order condition for an I-projection](first-order-condition-for-i-projections.md)
- [Divergence defect as a first-order term](divergence-defect-as-a-first-order-term.md)
- [Pythagorean identity at an algebraic inner point](pythagorean-identity-at-an-inner-point.md)
- [Pythagorean identity for linear families](pythagorean-identity-for-linear-families.md)
- [Tangent line of $x \log x$](tangent-line-of-x-log-x.md)
- [Splitting a divergence term](splitting-a-divergence-term.md)
- [First-order estimate along a segment, one letter](first-order-estimate-along-a-segment.md)

## Related topics

- [Method of types](../../entropy-and-mutual-information/method-of-types/README.md): Sanov's theorem
  identifies $D(\Gamma\|Q)$ as the exponent of $Q^n\{P_x \in \Gamma\}$, and the I-projection is the
  limiting conditional law in Gibbs' conditioning principle.
- [Shannon entropy and Kullback–Leibler divergence](../../entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/README.md):
  the divergence being minimised, and Gibbs' inequality $D \ge 0$.
- [Csiszár–Kullback–Pinsker inequality](../csiszar-kullback-pinsker.md): converts the divergence
  bounds of the Pythagorean inequality into total-variation bounds.
- [Data-processing inequality](../data-processing-inequality/README.md): monotonicity of divergences
  and mutual information under Markov kernels.
