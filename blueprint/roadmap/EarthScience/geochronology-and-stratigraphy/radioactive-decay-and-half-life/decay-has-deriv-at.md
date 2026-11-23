# Decay has Deriv At

Radioactive decay: `N(t) = N0 * exp(-λ*t)` solves `N' = -λ*N`. This is the
bolus case (`R = 0`) of `CompartmentKinetics.hasDerivAt_amount`, via
`CompartmentKinetics.amount_bolus`; it is not a new exponential-decay derivative.
