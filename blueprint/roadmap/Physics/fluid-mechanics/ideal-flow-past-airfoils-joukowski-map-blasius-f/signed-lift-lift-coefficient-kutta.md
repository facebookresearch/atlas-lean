# Signed Lift lift Coefficient kutta

Kutta-selected signed lift, lift coefficient, and small-angle
bound for the physical velocity, at any contour radius `R > 2 * a`.

The Blasius force value at radius `R` comes from the far-field
package through `blasiusForce_physicalVelocity`. With chord
`c = 4 * a`, the signed lift is `-ρ * U * Γ` at the Kutta
circulation `Γ = -4 * π * a * U * sin α`, the lift coefficient is
`2 * π * sin α`, and it differs from `2 * π * α` by at most
`π * |α|^3 / 3`.
