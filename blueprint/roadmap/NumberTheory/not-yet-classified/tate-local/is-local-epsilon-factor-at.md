# Local epsilon factor

`ε` is the local epsilon factor of `χ` at `v` and `s`, for the
additive character `ψ` and the additive Haar measure `μ`, when
`ε = γ * L(χ, s) / L(χ⁻¹, 1 - s)` for the local gamma factor `γ` (`IsLocalGammaFactor`, which
includes Tate's convergence and character conditions). The `L`-factors are the values of
`localLFactorAt`, which are `0` at their poles; in the range of absolute convergence that
`IsLocalGammaFactor` requires, neither of them has a pole, so this convention does not
enter.
