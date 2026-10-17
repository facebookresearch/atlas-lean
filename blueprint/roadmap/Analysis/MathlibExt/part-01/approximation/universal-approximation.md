---
article_id: af_dcc284004146daa477b1b7d8
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.universal_approximation
---

# Universal Approximation

Universal approximation theorem (`universal-approximation-s1` from
https://en.wikipedia.org/wiki/Universal_approximation_theorem): a single-hidden-layer
feedforward network with activation `σ` maps `x` to
`∑ i, c i * σ (@inner ℝ _ _ (W i) x + b i)`; if `σ` is continuous and non-polynomial,
such networks are dense in `C(K)` under the uniform norm on every compact `K`.
This is the continuous-activation case of the theorem of M. Leshno, V. Ya. Lin, A. Pinkus and
S. Schocken, *Multilayer feedforward networks with a nonpolynomial activation function can
approximate any function*, Neural Networks 6(6) (1993), 861–867,
doi:10.1016/S0893-6080(05)80131-5, which allows any locally bounded, piecewise continuous
activation that is not almost everywhere equal to a polynomial; for continuous `σ` this is the
same as the pointwise hypothesis `_hnp`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.Approximation.UniversalApproximation](../../../../../sources/v2/MathlibExt.md)
