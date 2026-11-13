# Estimating the shape does not change the `β`-block of the inverse Fisher information

If
the fixed-shape Fisher information `A = Xᵀ diag(F) X` is invertible and the total shape information
`D = ∑ᵢ nbShapeFisherInfo θ ηᵢ` is nonzero, the inverse of the joint Fisher information is
`[[A⁻¹, 0], [0, D⁻¹]]`. So the asymptotic covariance `A⁻¹` that the information assigns to `β̂` is
the same whether `θ` is known or estimated jointly.
