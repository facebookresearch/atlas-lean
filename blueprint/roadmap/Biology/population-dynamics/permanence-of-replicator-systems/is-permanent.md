# Is Permanent

The replicator equation of the matrix game `A` is **permanent**: there is `δ > 0` such that
every solution `x` on `[0, ∞)` (`IsSolution (fun z => A *ᵥ z) x`) starting in the interior of the
simplex (every `xᵢ(0) > 0`, `∑ xᵢ(0) = 1`) eventually has every coordinate at least `δ`: some `T`
has `xᵢ(t) ≥ δ` for all `t ≥ T` and all `i`.
