# Virtual work identity on a box

Let `[a, b] ⊂ ℝ³` be a box with `a_i < b_i` for every `i`, `U` an open set containing it, `σ` a
stress field whose components are continuously differentiable on `U` and which is
[symmetric](../cauchy-stress-small-strain-and-mohr-s-circle/is-symmetric-stress.md) at every point
of the box, `v` a continuously differentiable virtual displacement on `U`, and `body` a body force
with `div σ + body = 0` on the box, where `div σ` is the [stress divergence](stress-divergence.md).
Then `∫_{[a,b]} σ : ε(v) = ∫_{[a,b]} body · v + W`, where `ε(v)` is the
[small strain](../cauchy-stress-small-strain-and-mohr-s-circle/small-strain.md) of the
[displacement gradient](../cauchy-stress-small-strain-and-mohr-s-circle/displacement-gradient.md) of
`v` and `W` is the [boundary work](box-traction-work.md) of the tractions with outward normals.
