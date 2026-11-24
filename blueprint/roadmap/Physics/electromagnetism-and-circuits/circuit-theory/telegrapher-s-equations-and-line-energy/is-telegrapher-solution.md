# Solution of the telegrapher equations on a set

For real per-unit-length constants `R`, `L`, `G` and `C` (resistance, inductance, conductance and
capacitance), a set `U` of points `(x, t)` and real functions `v` and `i` of `(x, t)` (voltage and
current), the pair `(v, i)` solves the telegrapher equations on `U` when at every `(x, t) ∈ U`

`∂ₓv(x, t) = −R i(x, t) − L ∂ₜi(x, t)` and `∂ₓi(x, t) = −G v(x, t) − C ∂ₜv(x, t)`.

The partial derivatives are derivatives of the slices `y ↦ v(y, t)` and `s ↦ v(x, s)`, taken as `0`
where the slice is not differentiable.
