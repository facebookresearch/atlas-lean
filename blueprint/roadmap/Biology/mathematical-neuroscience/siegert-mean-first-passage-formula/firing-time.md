# Firing Time

The **firing time** (first-passage infimum): Mathlib's `hittingAfter` of the membrane voltage
`V(t)` to `[θ, ∞)` starting from `0`, taking values in `WithTop ℝ≥0` (`⊤` if the hit set
`{t ≥ 0 | θ ≤ V(t)}` is empty). For an arbitrary path this is the infimum of the hit set (not
necessarily attained at that time for discontinuous paths); for continuous paths it is the first
time `V(t) ≥ θ`.
