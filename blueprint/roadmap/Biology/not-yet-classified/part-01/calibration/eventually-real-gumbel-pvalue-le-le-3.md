# Asymptotic validity, lattice scores

In the null model of i.i.d. lattice Cramér scores
with renewal input `R` and `C > 0`, the Karlin–Altschul p-value `pₙ = 1 - exp (-K n e^{-θ Mₙ})`
(built from the lower lattice bound) is asymptotically conservative: for every `α ∈ [0, 1]` and
`ε > 0`, eventually `P(pₙ ≤ α) ≤ α + ε`. Exact calibration is not claimed: the underlying
probabilities have no limit (`LatticeRenewalInput.not_tendsto`).
