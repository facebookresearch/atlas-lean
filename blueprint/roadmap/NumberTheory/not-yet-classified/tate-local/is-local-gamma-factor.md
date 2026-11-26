# Local gamma factor

`γ` is the local gamma factor of `χ` at `s`, for the additive
character `ψ` and the additive Haar measure `μ`: the data are admissible
(`IsLocalZetaAdmissible`: continuous characters, `ψ` nontrivial, and both zeta integrals
absolutely convergent for every test function), and Tate's local functional equation
`Z(f̂, χ⁻¹, 1 - s) = γ * Z(f, χ, s)`, with `f̂ = tateFourier ψ μ f`, holds for every test
function `f`. By `IsLocalGammaFactor.eq_div` it does not depend on the test function. Values
of `s` outside the range of absolute convergence, where the gamma factor is defined by
meromorphic continuation, are outside its scope.
