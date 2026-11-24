# Uniform Beam Moment eq iterated Deriv

The bending moment in the canonical iterated-derivative
form used by the `EulerBernoulliBeam` API:
`M = -EI * iteratedDeriv 2 y`. This is the same function as
`uniformBeamMoment`, whose definition uses nested `deriv`;
the bridge lets clients move between the two encodings.
