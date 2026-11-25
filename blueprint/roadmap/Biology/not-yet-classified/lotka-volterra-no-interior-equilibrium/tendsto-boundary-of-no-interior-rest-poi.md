# Convergence to the boundary of the simplex

**Convergence to the boundary of the simplex** (Hofbauer and Sigmund 2003, §3): let `A` be a
real square matrix indexed by a finite type, and suppose the replicator equation
`xᵢ' = xᵢ ((A x)ᵢ - xᵀ A x)` (`IsSolution (fun z => A *ᵥ z)`) has no rest point in the interior
of the simplex: no `z` with every `zᵢ > 0`, `∑ zᵢ = 1` and `IsRestPoint (fun z => A *ᵥ z) z`
(that is, `zᵢ ((A z)ᵢ - zᵀ A z) = 0` for every `i`). Then every solution `x` on `[0, ∞)` with
`x(0)` in the interior of the simplex converges to the boundary: `∏ᵢ xᵢ(t) → 0` as `t → ∞`.

## Sources

- Hofbauer and Sigmund (2003), §3.
