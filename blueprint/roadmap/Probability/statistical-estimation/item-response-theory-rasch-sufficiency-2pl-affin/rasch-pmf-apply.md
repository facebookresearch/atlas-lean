# Rasch PMF apply

Assume that equality on `ι` is decidable and that `ι` is finite.

Mass of a response pattern under the Rasch model.

In symbols: `raschPMF b θ x = ∏ i, (if x i then ENNReal.ofReal (Real.sigmoid (θ - b i)) else ENNReal.ofReal (1 - Real.sigmoid (θ - b i)))`.
