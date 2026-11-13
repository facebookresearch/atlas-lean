# Singular covariance

`det S = 0` iff the samples lie in an affine hyperplane
`{x | x ⬝ w = c}` with `w ≠ 0` (for every `n`). Contrast: `det (Xᵀ X) = 0` iff they lie in a
hyperplane through the origin, so data on an affine hyperplane missing the origin have a
singular `S` but a nonsingular second moment (see the test file).
