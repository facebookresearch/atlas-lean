# Blasius Force physical Velocity

Bridge from the far-field package to the force value used below:
for the physical velocity at any circulation `Γ` and any contour
radius `R > 2 * a`, the Blasius force is `I * ρ * U * Γ * exp (-α * I)`.
This combines `JoukowskiBranch.exists_physicalVelocity_farField` with
`BlasiusForce.blasiusForce_eq`, taking the decomposition remainder to
be the difference from the two-term far-field expansion.
