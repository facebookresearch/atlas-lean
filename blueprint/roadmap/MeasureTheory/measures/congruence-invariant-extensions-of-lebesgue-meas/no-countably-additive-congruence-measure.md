# No countably additive congruence-invariant measure on all plane sets

The countably additive reading is false in ZFC. Sketch: let
`V₀ ⊆ [0,1]` meet each `ℚ`-coset of `ℝ` exactly once (Vitali selector)
and put `V = V₀ × [0,1]`. Enumerating `ℚ ∩ [-1,1]` as `(qₙ)`, the
translates `Tₙ = V + (qₙ, 0)` are pairwise disjoint, each congruent to
`V`, so all have the same mass `c = μ V`. Their union contains the unit
square `Q = [0,1] × [0,1]` and lies in the strip `[-1,2] × [0,1]` of
volume 3, so countable additivity and monotonicity give
`1 = μ Q ≤ μ U ≤ 3`, while countable additivity also gives
`μ U = ∑'ₙ c`, which is `0` if `c = 0` and `+∞` if `c > 0`, a
contradiction. Hence no such `μ` exists. This refutes the countably
additive formalization only. The typescript says bare "additive"; the
finite-additivity reading is Banach's 1923 theorem (a Banach measure: a
finitely additive, isometry-invariant function on all plane sets
extending Lebesgue measure), not this claim, and is not asserted here.

## Sources

- E. Szpilrajn, Problem 169 of the Scottish Book; typescript PDF p.78, printed p.75. Banach, Fund. Math. 4 (1923), 7-33.
