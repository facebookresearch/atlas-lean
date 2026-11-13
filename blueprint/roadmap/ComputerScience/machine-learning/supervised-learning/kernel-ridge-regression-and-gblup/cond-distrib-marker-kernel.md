# The GBLUP posterior

If the genetic values `Z' β` of individuals with genotypes `Z'` and
the phenotypes `y = Z β + ε` of the training individuals are jointly Gaussian with the covariance
of the marker kernel (marker-effect variance `s > 0`, residual variance `σ² > 0`), then given `y`
the genetic values are Gaussian with mean `Z' Zᵀ (ZZᵀ + (σ²/s) I)⁻¹ y`, which is the RR-BLUP
prediction `Z' β̂` (`gpMean_markerKernel_mulVec`), and covariance
`s (Z' Z'ᵀ - Z' Zᵀ (ZZᵀ + (σ²/s) I)⁻¹ Z Z'ᵀ)`.
