# Intensity Level

Sound intensity level of intensity `I` against reference intensity
`Iref`, in decibels: `10 * log10 (I / Iref)`. Physically meaningful only
for positive `Iref` and `I` in the same unit; the totalized `Real.logb`
value outside that domain (for example at `I = 0`) is not a level.
