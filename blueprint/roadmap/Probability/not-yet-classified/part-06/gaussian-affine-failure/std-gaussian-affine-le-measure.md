# Std Gaussian affine le measure

Affine half-space probability for the standard Gaussian on
`EuclideanSpace ℝ (Fin n)`.

For a nonzero continuous linear functional `L`, the affine
variable `a + L Z`, with `Z` standard Gaussian, has Gaussian law
with mean `a` and standard deviation `‖L‖`; hence
`P(a + L Z ≤ t) = Φ((t - a) / ‖L‖)`, where `Φ` is the standard
normal cdf. This is the Euclidean dual-norm form: the variance
is the squared operator norm of `L`, not a coordinate sup norm.
