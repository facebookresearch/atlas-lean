# Carnot Efficiency

The Carnot efficiency `1 - Tc / Th` of a reversible engine operating between a cold
reservoir at absolute temperature `Tc` and a hot reservoir at absolute temperature `Th`.
Physical domain: `0 ≤ Tc ≤ Th` with `0 < Th`, where the value lies in `[0, 1]`; the engine
results use `0 < Tc ≤ Th` and the reversible cycle `0 < Tc < Th`. Other values are
nonphysical: `Tc > Th` gives a negative value, a negative `Tc` a value above `1`, and at
`Th = 0` Lean's `x / 0 = 0` gives the junk value `1`. The lemmas that read it assume `0 < Tc`
and `Tc ≤ Th`.
