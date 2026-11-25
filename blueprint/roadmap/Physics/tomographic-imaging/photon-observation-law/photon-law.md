# Photon count law of a CT design

For finite index types `ι` (rays) and `κ` (cells), source intensities `I0 :
ι → ℝ≥0`, a real design matrix `A : Matrix ι κ ℝ` and attenuation
coefficients `x : κ → ℝ`, the photon law is the probability measure on count
vectors `ι → ℕ` that is the product over rays `j` of Poisson distributions
with rates `I0 j * exp(-(A *ᵥ x) j)`: independent Poisson counts, one per
ray.
