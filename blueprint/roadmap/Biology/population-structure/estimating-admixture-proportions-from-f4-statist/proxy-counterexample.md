# Example of a proxy that fits although the target is not mixed from it

Let `α ≠ 0` and let `M` be a [drift model](../patterson-s-f-statistics/drift-model.md) on a measure
`μ`, with eight edges and seven populations, whose lineage weights `w` are the
[proxy table](proxy-weight.md) with parameter `α` and whose edge lengths are all `1`. Take the
target `T = 3` and the right populations `(R₀, R₁, R₂) = (4, 5, 6)`. Then

- the [source matrices](qp-adm-source-matrix.md) of the sources `(S₀, S₁') = (0, 2)` and
  `(S₀, S₁) = (0, 1)` are equal, and so are the [target vectors](qp-adm-target-vector.md) of `T`;
- the [qpWave matrices](../abba-baba-test-and-f-statistic-estimators/f4-matrix.md) of the left
  populations `(S₀, T, S₁')` and `(S₀, T, S₁)` are equal;
- with the sources `(S₀, S₁')`, the only solution of the system is the weight `α` on `S₁'`, so
  with either list of sources it is `α`;
- the target is the mixture `w T = α w S₁ + (1 - α) w S₀`;
- for no real `γ` is `w T = γ w S₁' + (1 - γ) w S₀`.
