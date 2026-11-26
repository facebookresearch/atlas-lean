# Has Semialgebraic Projections

Semialgebraic subsets of the coordinate spaces over `R` *have semialgebraic projections* if,
for every `n`, forgetting the coordinate `0` (`Fin.tail`) maps semialgebraic subsets of
`Fin (n + 1) → R` to semialgebraic subsets of `Fin n → R`. For `R = ℝ` this is the
Tarski–Seidenberg theorem, proved by cylindrical algebraic decomposition in
`TauCeti.Geometry.RealAlgebraic.CAD.Existence`. It fails for some ordered fields: over `ℚ`,
forgetting `t` maps the parabola `{(t, x) | t ^ 2 = x}` to the set of rational squares, which is
dense and codense in the positive rationals and so is not semialgebraic.
