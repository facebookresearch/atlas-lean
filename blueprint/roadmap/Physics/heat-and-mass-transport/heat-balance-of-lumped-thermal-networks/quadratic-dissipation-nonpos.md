# Symmetric G ≥ 0, g0 ≥ 0, no heating: the derivative is nonpositive

Let `ι` be a finite index set of zones, with capacities `C i` of any sign, symmetric conductances
`G i j = G j i`, boundary conductances `g0 i` and a constant outside temperature `Tout`. Let
`G i j ≥ 0` and `g0 i ≥ 0`, and let the zone temperatures `T i` have derivatives `Tv i(t)` and
satisfy the zone equations without heating,
`C i Tv i(t) = ∑_j G i j (T j(t) - T i(t)) + g0 i (Tout - T i(t))`, at every time. Then at every `t`
the functional `V(s) = (1/2) ∑_i C i (T i(s) - Tout)²` has the derivative

`-((1/2) ∑_i ∑_j G i j (T j(t) - T i(t))² + ∑_i g0 i (T i(t) - Tout)²)`,

and this derivative is `≤ 0`. That `V` is [nonincreasing](quadratic-dissipation-antitone.md) is a
separate statement.
