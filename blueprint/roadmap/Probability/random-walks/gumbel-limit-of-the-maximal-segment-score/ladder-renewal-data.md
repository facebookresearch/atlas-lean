# Ladder renewal data for nonlattice scores

For a measure `P` on `Ω`, a real random variable `Y` and a real `θ`, nonlattice ladder renewal data
consist of a [descending-ladder fixed point](ladder-fixed-point.md) `(D, M')` for `Y` and a finite
measure `G` on `ℝ` (the defective law of the first strict ascending ladder height) with: `G`-almost
every `y` nonnegative; the ladder Cramér identity `∫ e^{θ y} dG(y) = 1`; `y e^{θ y}` integrable for
`G` (a finite tilted ladder mean); and the defective renewal equation
`P(M' > t) = ∫ P(M' > t - y) dG(y)` for every `t ≥ 0`. In the intended reading these come from
cutting `M'` at its first ascending ladder epoch (strong Markov property) and from Wald's identity
for `e^{θ S_n}`; the structure takes them as hypotheses.
