# Validity from a dominating reference tail

Let `μ` be a measure on `Ω`, not necessarily a probability measure, `T : Ω → ℝ` the statistic of a
test that rejects for large values, and `G : ℝ → ℝ` a nonincreasing function, the reference upper
tail. If `G` dominates the tail of `T` under `μ`, `μ{ω : s ≤ T ω} ≤ max(G s, 0)` for every real
`s` (so where `G s < 0` it asks `μ{s ≤ T} = 0`), then the reported p-value `ω ↦ G (T ω)` is
[valid](../valid-p-values-and-false-discovery-proportion/is-valid-pvalue.md):
`μ{ω : G (T ω) ≤ t} ≤ t` for every `t ∈ [0, 1]`. No measurability of `T` and no continuity of `G`
is assumed.

The event `{G (T ω) ≤ t}` is `{T ∈ A}` for the upper set `A = {s | G s ≤ t}`, which is empty,
`[a, ∞)`, `(a, ∞)` or `ℝ`; in the last two cases it is an increasing union of events `{s_n ≤ T}`
with `s_n ∈ A`, each of measure at most `max(G s_n, 0) ≤ t`, since `G s_n ≤ t` and `t ≥ 0`.

## Sources

- Lehmann–Romano (2005), Lemma 3.3.1, stated there for the exact tail.
