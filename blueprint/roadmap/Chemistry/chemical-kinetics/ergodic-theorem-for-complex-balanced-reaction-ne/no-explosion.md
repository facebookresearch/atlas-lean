# Non-explosion of a process on molecule counts

Let `S` be a finite set, `P` a measure on `Ω` and `X : ℝ × Ω → ℕ^S` a process. `X` does not
explode when, for `P`-almost every `ω`, the total molecule count `∑_{i ∈ S} X_s(ω)_i` is bounded
for `s` in `[0, t]`, for every real `t` (for `t < 0` the interval is empty): no path blows up in
finite time. Neither measurability of `X` nor total mass one of `P` is required.

It holds, for example, when almost every path takes finitely many values on each interval
`[0, t]`, as a path with finitely many jumps in bounded time intervals does. For the path of the
jump–hold chain of a stochastic reaction network, it follows from the jump times tending to `∞`
almost surely ([non-explosion in this form](../regeneration-of-stochastic-reaction-networks/no-explosion-path.md)).
