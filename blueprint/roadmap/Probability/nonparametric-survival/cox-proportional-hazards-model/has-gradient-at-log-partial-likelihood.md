# The Cox score vector is the gradient of the log partial likelihood

The gradient needs an
inner product, which `Fin p → ℝ` (sup norm) lacks, so the statement transports `ℓ` to Euclidean
space `EuclideanSpace ℝ (Fin p)` along `WithLp.ofLp`.
