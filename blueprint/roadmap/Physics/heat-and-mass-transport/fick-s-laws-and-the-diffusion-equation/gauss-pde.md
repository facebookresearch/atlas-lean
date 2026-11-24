# For D > 0 and t > 0 the Gaussian solves the diffusion equation

Let `D > 0` and `t > 0`. For all real `M` and `x`, the [Gaussian](gauss.md)
`G(x, t) = M/√(4πDt) · exp(-x²/(4Dt))` satisfies

`∂G/∂t(x, t) = D ∂²G/∂x²(x, t)`,

the derivatives existing by the [time derivative](gauss-tderiv-value.md) and the
[second spatial derivative](gauss-xxderiv-value.md). It is a special case of the
[point-release kernel solving advection–diffusion–reaction](../point-release-solution-of-advection-diffusion-re/point-release-solves-adr.md),
with no drift and no reaction.
