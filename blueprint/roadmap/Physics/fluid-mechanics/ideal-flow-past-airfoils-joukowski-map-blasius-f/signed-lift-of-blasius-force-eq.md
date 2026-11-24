# Signed Lift of blasius Force eq

Signed lift from the Blasius force value. If the contour force
for `physicalVelocity a U Γ α` is `I * ρ * U * Γ * exp (-α * I)`,
then rotating that complex force by `exp (α * I)` gives
`I * ρ * U * Γ`; hence the component perpendicular to the free
stream, with the sign convention in `signedLift`, is `-ρ * U * Γ`.
No positivity or nonvanishing hypothesis is needed for this
algebraic step.
