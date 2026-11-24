# Admission

For a nondecreasing cumulative departure count `D`, the vehicle that enters
at time `t` has a finite exit time if and only if the departure count reaches its number
`N0 + A t` at some time. Otherwise the vehicle never leaves and its exit time is `⊤`: a missing
finite exit time is reported, not replaced by an arbitrary value. It transports
`MeasureTheory.hittingAfter_eq_top_iff`; monotonicity of `D` removes the restriction to times
after the entry.
