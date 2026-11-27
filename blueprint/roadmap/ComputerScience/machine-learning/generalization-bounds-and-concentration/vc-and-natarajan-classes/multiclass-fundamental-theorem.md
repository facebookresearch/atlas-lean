# Multiclass fundamental theorem (Natarajan bounds)

Let $H \subseteq [k]^X$ be nonempty with $k \ge 2$ finite and Natarajan dimension $d < \infty$, under 0-1 loss and the
measurability conditions of the source. There are absolute constants $C_1, C_2 > 0$ such that:

1. the uniform-convergence sample complexity is at most $\lceil C_2 (d \log k + \log(2/\delta))/\varepsilon^2 \rceil$,
   and the agnostic PAC sample complexity is at most $\lceil C_2 (d \log k + \log(1/\delta))/\varepsilon^2 \rceil$;
2. for $d \ge 1$ the realizable PAC sample complexity is at most
   $\lceil C_2 (d \log(k d/\varepsilon) + \log(1/\delta))/\varepsilon \rceil$; for $d = 0$ the class has one hypothesis and
   learning needs no samples;
3. for $d \ge 2$ and $\varepsilon$, $\delta$ below absolute constants, the agnostic and uniform-convergence sample
   complexities are at least $C_1 (d + \log(1/\delta))/\varepsilon^2$ and the realizable one is at least
   $C_1 (d + \log(1/\delta))/\varepsilon$, by reduction to the binary case.

Classes with $d \le 1$ need their own lower-bound conditions, and learning sample complexity is not the same as
uniform-convergence sample complexity.

## Expansion

This node states a precise result.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Natarajan dimension and Natarajan lemma.

## Proof depends on

- [VC classes have uniform convergence (upper half of the quantitative fundamental theorem)](vc-classes-have-uniform-convergence.md)

## Sources

- S. Shalev-Shwartz and S. Ben-David, *Understanding Machine Learning: From Theory to Algorithms*, Cambridge University Press, 2014 (author copy), Theorem 29.3 (the multiclass fundamental theorem) and Section 29.2.1 (lower bounds by reduction to the binary theorem; upper bounds along Chapter 28 with the Natarajan lemma). The source states its lower bounds without the nondegeneracy conditions of item 3, which they need. <https://www.cs.huji.ac.il/~shais/UnderstandingMachineLearning/understanding-machine-learning-theory-algorithms.pdf>
