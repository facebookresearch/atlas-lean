# First Passage Time

The **interspike interval** (first-passage infimum): Mathlib's `hittingAfter` of the
displacement `c t + √2 B(t)` to `[z₀, ∞)` starting from `0`, taking values in `WithTop ℝ≥0` (`⊤`
if the hit set `{t ≥ 0 | z₀ ≤ c t + √2 B(t)}` is empty). For an arbitrary path this is the
infimum of the hit set (not necessarily attained at that time, e.g. for a discontinuous path below
`z₀` at `0` and above `z₀` for all `t > 0`); for continuous paths it is the first hitting time.
