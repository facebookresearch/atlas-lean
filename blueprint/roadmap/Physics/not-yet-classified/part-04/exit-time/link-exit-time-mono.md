# FIFO: no overtaking

If the cumulative arrival count `A` is nondecreasing, the exit
time `linkExitTime N0 A D t` is nondecreasing in the entry time `t`: a vehicle that enters later
leaves no earlier. This holds for every departure count `D` and every initial count `N0`, as an
order statement in `WithTop ℝ≥0`, so an entry with no finite exit time is followed only by
entries with none. It transports `MeasureTheory.hittingAfter_mono` (a later start time) and
`MeasureTheory.hittingAfter_anti` (a higher vehicle number).
