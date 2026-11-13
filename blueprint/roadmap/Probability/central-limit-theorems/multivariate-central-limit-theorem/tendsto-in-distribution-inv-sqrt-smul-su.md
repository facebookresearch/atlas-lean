# Multivariate central limit theorem

**Multivariate central limit theorem** (interface form). Let `X : ℕ → Ω → E` be i.i.d.
square-integrable random vectors in a finite-dimensional real inner product space with mean
`μ := ∫ ω, X 0 ω ∂P`. If `Y : Ω' → E` is a random vector all of whose scalar projections `⟪Y, t⟫`
are centered real Gaussians with variance `Var[⟪X 0, t⟫]`, then
`(√n)⁻¹ • (∑ k ∈ range n, X k - n • μ)` converges in distribution to `Y`.

The covariance of `X 0` may be singular: a projection with variance `0` has the Dirac mass at `0`
as its limit law, which is `gaussianReal 0 0`.
