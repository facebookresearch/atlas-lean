# The Pearson residual vector is asymptotically a singular multinomial Gaussian

For
i.i.d. categorical observations with all cell probabilities `pᵢ > 0`, the Pearson residuals
`((Nᵢ - n pᵢ) / √(n pᵢ))ᵢ` converge in distribution to `P_K Z`, where `Z` is standard Gaussian
on `EuclideanSpace ℝ ι` and `P_K` is the orthogonal projection onto the hyperplane
`K = (√p)ᗮ`. The limit covariance `I - √p √pᵀ` is singular (the limit is orthogonal to `√p`);
no invertibility of the multinomial covariance is used.
