# The raw residual-product second moment of the marginal estimates

**The raw residual-product second moment of the marginal estimates** (Zhu and Stephens
2017): if `𝔼[ε_i ε_i'] = σ² [i = i']`, then
`𝔼[(β̂_j - (R β)_j)(β̂_k - (R β)_k)] = σ² / N · R_jk`.

This theorem deliberately assumes neither that `P` is a probability measure nor that the noise
has mean zero, so its conclusion is not by itself a covariance or a Gaussian likelihood. With a
probability measure and mean-zero noise, `integral_marginalEffect` identifies `R β` as the mean,
and this raw second moment is the corresponding covariance.
