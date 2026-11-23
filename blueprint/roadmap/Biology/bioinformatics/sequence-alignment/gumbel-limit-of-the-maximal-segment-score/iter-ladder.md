# A path functional evaluated on the i-th ladder excursion

For a functional `φ` of paths `ℕ → ℝ`, its value on the `i`-th ladder excursion is defined by
restarting the path at the [first descending ladder epoch](desc-ladder-epoch.md): `φ₀(x) = φ(x)`
and `φ_{i+1}(x) = φ_i(x')`, where `x'` is the [path seen from time](path-shift.md) `τ₋ x`. Unfolded,
`φ_i(x) = φ` of the path seen from the `i`-th [ladder epoch](ladder-epoch.md) `T_i`.
