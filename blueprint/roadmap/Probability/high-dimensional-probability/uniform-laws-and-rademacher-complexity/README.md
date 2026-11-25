# Uniform laws and Rademacher complexity

A uniform law of large numbers bounds the deviation of empirical means from their expectations
simultaneously over a class of functions, $\|P_n - P\|_{\mathcal{F}} =
\sup_{f \in \mathcal{F}} |P_n f - P f|$. Symmetrization compares this deviation with the
Rademacher complexity of the class, the expected supremum of a sign-randomized empirical sum, and
the bounded differences inequality makes the comparison hold with high probability. These are the
tools behind generalization bounds in learning theory (Wainwright, *High-Dimensional Statistics*,
2019, Chapter 4).

- [Uniform deviation of empirical means](uniform-deviation.md)
- [Measurability of the uniform deviation](measurable-uniform-deviation.md)
- [Bounded differences of the uniform deviation](abs-uniform-deviation-update-sub-le.md)
- [Rademacher complexity](rademacher-complexity.md)
- [Symmetrization bound](integral-uniform-deviation-le-two-mul-ra.md)
- [Concentration of the uniform deviation](uniform-deviation-le-integral-uniform-de.md)
- [Uniform law via Rademacher complexity](uniform-deviation-le-two-mul-rademacher.md)

## Related topics

- [McDiarmid's inequality](../../concentration-inequalities/mcdiarmid-s-inequality/README.md)
- [Generalization bounds and concentration](../../../ComputerScience/machine-learning/generalization-bounds-and-concentration/README.md)
- [Glivenko–Cantelli theorem](../../nonparametric-survival/glivenko-cantelli-theorem/README.md)
- [Generic chaining and Gaussian processes](../generic-chaining-and-gaussian-processes/README.md):
  conditionally on the sample, a Rademacher average is a sub-Gaussian process, so its expected
  supremum is bounded by chaining.
