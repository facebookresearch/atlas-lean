# Is Permanent

The replicator equation of the matrix game `A` is **permanent**: there is `δ > 0` such that
every solution `x` (`IsSolution (fun z => A *ᵥ z) x`) starting in the interior of the simplex
(every `xᵢ(0) > 0`, `∑ xᵢ(0) = 1`) eventually has every coordinate at least `δ`: some `T` has
`xᵢ(t) ≥ δ` for all `t ≥ T` and all `i`. Here `IsSolution` asks for two-sided derivatives at
every `t ≥ 0`, `t = 0` included: a trajectory given only on `[0, ∞)` must be extended to negative
times with the replicator derivative at `0`.
