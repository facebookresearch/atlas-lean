# Ladder renewal data, lattice case

**Ladder renewal data, lattice case** with span `h`, for an excursion height `Y` and Cramér
root `θ`: the descending-ladder fixed point with `D` on the lattice `-hℕ`, and the lattice
ascending-ladder renewal structure of `M'` (strong Markov property), taken as hypotheses.
`g j` is the defective probability that the first strict ascending ladder height equals `j h`;
cutting `M'` at the first ascending ladder epoch gives the defective renewal equation
`P(M' > k h) = ∑_{j > k} g j + ∑_{j ≤ k} g j P(M' > (k - j) h)` (`IsRenewalSolution`); the
ladder Cramér identity is `∑ g j e^{θ h j} = 1`; the ladder support is aperiodic; and the tilted
ladder mean is finite. These are exactly the inputs of `tendsto_exp_mul_maxTail`, whose
discrete key renewal theorem is proved, so no renewal theorem is assumed in the lattice case.
