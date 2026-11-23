# Validity from a dominating reference tail

Let a test reject for large values of a
statistic `T` and report `G (T ω)`, where `G` is antitone. If `G` dominates the null tail of `T`,
`μ {s ≤ T} ≤ G s` for every `s`, then `G ∘ T` is a valid p-value: `μ {G ∘ T ≤ t} ≤ t` for
`t ∈ [0, 1]`. No measurability or continuity is needed.

The event `{G (T ω) ≤ t}` is `{T ∈ A}` for the upper set `A = {s | G s ≤ t}`, which is either
empty, `[a, ∞)`, `(a, ∞)` or `ℝ`; in the last two cases it is an increasing union of events
`{s_n ≤ T}` with `s_n ∈ A`, and continuity from below finishes.

## Sources

- Lehmann–Romano (2005), Lemma 3.3.1, stated there for the exact tail.
