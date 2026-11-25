# Bar functions vanishing at both ends with square-integrable derivative

For a real number `L` (the bar length, intended `L > 0`), an element of `H¹₀(0, L)` consists of a
representative `v : ℝ → ℝ` and a weak derivative `v' : ℝ → ℝ` such that `v'` is square integrable on
`[0, L]`, `v(x) = ∫_0^x v'(t) dt` for every `x ∈ [0, L]`, and `∫_0^L v'(t) dt = 0`, the end
condition: for `L ≥ 0`, `v(0) = v(L) = 0` ([end values](to-fun-zero-and-length.md)). Values outside
`[0, L]` are unconstrained. This is the encoding of the
[unit-interval space](../../../Analysis/partial-differential-equations/weak-solutions-of-elliptic-equations/weak-h10.md)
on `[0, L]`.
