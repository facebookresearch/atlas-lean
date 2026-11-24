# Link Exit Time

Exit time of the vehicle that enters the link at time `t`, under first-in-first-out order:
the infimum of the times `≥ t` at which the cumulative departure count `D` reaches the
vehicle's number `N0 + A t`, and `⊤` if there is no such time; for right-continuous `D` this
infimum is attained and is the first such time. It is Mathlib's `MeasureTheory.hittingAfter` of the
deterministic process `D` (sample space `Unit`) into `Set.Ici (N0 + A t)` from the start time
`t`. Here `N0` is the number of vehicles on the link at time `0`, and `A`, `D` are the
cumulative arrival and departure counts from time `0`.
