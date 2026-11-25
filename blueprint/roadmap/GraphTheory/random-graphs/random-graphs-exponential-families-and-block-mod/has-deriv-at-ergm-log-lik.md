# Has Deriv At ergm Log Lik

Assume that equality on `V` is decidable; that `V` is finite; and that `ι` is finite.

Directional derivative of the log-likelihood is the score.

In symbols: `HasDerivAt (fun s : ℝ => ergmLogLik t (θ + s • v) y) (v ⬝ᵥ ergmScore t θ y) 0`.
