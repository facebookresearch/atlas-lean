# Hajek Projection

The Hájek projection of the U-statistic with kernel `h` of degree `m` on a sample of size
`n`: `θ̃ + (m / n) ∑_{i} (h̃₁(x_i) - θ̃)`, where `h̃ = (m!)⁻¹ ∑_σ h (· ∘ σ)` is the symmetrized
kernel, `θ̃ = E h̃` and `h̃₁ = hoeffdingProj μ h̃ 1` is its first projection.

The U-statistic only sees `h̃` (it averages over all injective index maps), so building the
projection, including its centring, from `h̃` makes this the projection of `uStatistic h` onto
sums of functions of single observations for an arbitrary, not necessarily symmetric, kernel.
In the usual regime where `h` is integrable, `E h̃ = E h`; Lean's totalized integral can differ
when `h` itself is not integrable, which is why the centring is `E h̃`. For a symmetric kernel
`h̃ = h` and this is `θ + (m / n) ∑_{i} (h₁(x_i) - θ)` with `θ = E h`
(`hajekProjection_eq_of_symm`). The intended regime is `m ≤ n`; for `m > n` the U-statistic is
`0` by convention and this is not its projection.
