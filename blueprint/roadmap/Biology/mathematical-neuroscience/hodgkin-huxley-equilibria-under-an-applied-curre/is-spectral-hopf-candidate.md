# Spectral Hopf conditions for an arrowhead matrix

For [arrowhead entries](arrow.md) and real `ω`, the spectral Hopf conditions at frequency `ω` for
the [arrowhead matrix](mat.md) `M` are:

- `ω > 0`;
- `i ω` and `-i ω` are complex eigenvalues of `M`;
- every complex eigenvalue `μ` of `M` with `Re μ ≥ 0` is `i ω` or `-i ω`;
- `χ'(i ω) ≠ 0`, where `χ'(μ) = 4 μ³ + 3 p₁ μ² + 2 p₂ μ + p₃` is the
  [termwise derivative formula](quartic-deriv.md) of the [characteristic quartic](char-q.md)
  `χ(μ) = μ⁴ + p₁ μ³ + p₂ μ² + p₃ μ + p₄`; as `i ω` is a [root](mem-spectrum-iff.md) of `χ`, this
  says that it is a simple root.

So `M` has a pair of conjugate eigenvalues on the imaginary axis and every other eigenvalue in the
open left half-plane, which makes it a Hopf candidate. No crossing of the imaginary axis as a
parameter varies is part of the conditions, so they do not by themselves give a Hopf bifurcation.
