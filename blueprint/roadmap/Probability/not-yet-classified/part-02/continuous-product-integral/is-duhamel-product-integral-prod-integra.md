# T44's grid product integral satisfies the Duhamel hypotheses

**T44's grid product integral satisfies the Duhamel hypotheses** on every total-variation
ball `{x | ∑ |x l| ≤ M}`, with Duhamel operator `gridDuhamel`, bound `k e^{2M}` and continuity
class `Set.univ`. This is a genuine instance of `IsDuhamelProductIntegral`; with
`IsDuhamelProductIntegral.hasHadamardDerivWithinAt` it recovers the Duhamel derivative
`duhamelDeriv` of T44 (via `gridDuhamel_self`).
