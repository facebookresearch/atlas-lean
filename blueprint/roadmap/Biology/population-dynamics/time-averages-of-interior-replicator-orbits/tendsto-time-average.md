# Convergence of time averages

**Convergence of time averages** (Schuster, Sigmund, Hofbauer and Wolff 1981, §5 B; Hofbauer
and Sigmund 2003, Theorem 4): let `A` be a real square matrix indexed by a finite type, and
suppose `p` is the unique interior rest point of the replicator equation
`xᵢ' = xᵢ ((A x)ᵢ - xᵀ A x)`. Let `x` be a solution (`IsSolution (fun z => A *ᵥ z) x`) with
`x(0)` in the interior of the simplex (every `xᵢ(0) > 0`, `∑ xᵢ(0) = 1`) that stays bounded
away from the boundary: there is `δ > 0` with `xᵢ(t) ≥ δ` for every `i` and every `t ≥ 0`. Then
for every `i`, the time average `(1/T) ∫₀ᵀ xᵢ(t) dt` converges to `pᵢ` as `T → ∞`. Here
`IsSolution` asks for two-sided derivatives at every `t ≥ 0`, `t = 0` included: a trajectory
given only on `[0, ∞)` must be extended to negative times with the replicator derivative at `0`.
Hofbauer and Sigmund (2003, Theorem 4) state this for permanent systems; the hypotheses
here are instead a unique interior rest point and an orbit bounded away from the boundary.

## Sources

- Schuster, Sigmund, Hofbauer and Wolff (1981), §5; Hofbauer and Sigmund (2003), Theorem 4.
