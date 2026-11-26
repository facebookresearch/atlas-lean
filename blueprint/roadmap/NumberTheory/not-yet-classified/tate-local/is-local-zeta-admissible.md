# Admissible data for Tate's local zeta integrals

The convergence and character
conditions of Tate's local functional equation: `K` is totally disconnected, so that the
locally constant test functions are its Schwartz--Bruhat functions; `ψ` is a continuous
nontrivial additive character; `χ` is a continuous character of `Kˣ`; and for every test
function `f` the integrands of `Z(f, χ, s)` and `Z(f̂, χ⁻¹, 1 - s)`, with
`f̂ = tateFourier ψ μ f`, are integrable for the multiplicative Haar measure, so both zeta
integrals converge absolutely. For a unitary `χ` these integrals converge when
`0 < re s < 1`. Outside the range of absolute convergence Tate's zeta integrals and gamma
factor are defined by meromorphic continuation, which this API does not cover; there the
Bochner integrals can be `0` although the integrals diverge, as for the trivial `χ` at
`s = 0` and the indicator of the valuation ring.
