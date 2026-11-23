# Derived nonlattice renewal input

From Cramér scores `hX` that are nonlattice (`hnl`), the
ladder input `L` (a `LadderInput`, taken as a hypothesis), nonlattice ladder renewal data `R`
for the first excursion height `L.Y 0` (strong-Markov consequences, taken as hypotheses),
and the key renewal theorem for the tilted ladder-height law (`hKRT`, assumed), this builds the
`NonlatticeRenewalInput` of the Gumbel limit with its tail hypothesis `tendsto_tail` *derived*
(renewal constant `C = R.tailConst`).
