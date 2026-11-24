# Physical-to-canonical bridge

The exit time of the vehicle that enters at `t` equals
the entry time plus the network-calculus virtual delay of the offset arrival count
`fun s => N0 + A s` against the departure count `D`, as an identity in `ℝ≥0∞` with no
hypotheses. Both sides are `⊤` exactly when the departure count never reaches `N0 + A t` at or
after `t`. This is the stated agreement of the two owner declarations,
`MeasureTheory.hittingAfter` and `Cslib.Algorithms.Networking.NetworkCalculus.delay`.
