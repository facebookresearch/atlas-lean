# Exact covariance propagation for affine maps

`covMatrix p (A *ᵥ X · + b) = A * covMatrix p X * Aᵀ`, with exactly this multiplication
order. The linear part is `FiniteProbability.covMatrix_mulVec`, valid for every weight; the
shift by `b` cancels in the centering, which needs total mass one.
