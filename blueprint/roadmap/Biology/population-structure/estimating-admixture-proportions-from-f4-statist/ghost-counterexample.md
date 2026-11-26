# Example where a ghost source is absorbed with weight twice its share

Let `α ≠ 0` and let `M` be a [drift model](../patterson-s-f-statistics/drift-model.md) on a measure
`μ`, with eight edges and seven populations, whose lineage weights `w` are the
[ghost table](ghost-weight.md) with parameter `α` and whose edge lengths are all `1`. Take the right
populations `(R₀, R₁, R₂) = (4, 5, 6)`, the sampled sources `(S₀, S₁) = (0, 1)`, the ghost `G = 2`
and the target `T = 3`. Then

- the right contrasts of `G` are twice those of `S₁`:
  `f4(G, S₀; R j, R₀) = 2 * f4(S₁, S₀; R j, R₀)` for `j = 1, 2`;
- the only solution of the system of the [source matrix](qp-adm-source-matrix.md) and the
  [target vector](qp-adm-target-vector.md) of `T` is the weight `2 α` on `S₁` (so `1 - 2 α` on
  `S₀`);
- the target is the mixture `w T = α w G + (1 - α) w S₀`;
- for no real `γ` is `w T = γ w S₁ + (1 - γ) w S₀`.

For `α = 3/4` the fitted weights are `-1/2` on `S₀` and `3/2` on `S₁`.
