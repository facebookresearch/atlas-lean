# Is Admissible Contact zero tangent iff

Frictionless slice: for `0 ≤ μ`, a contact state with zero tangent traction is admissible
exactly when `(N, g)` satisfies the scalar unilateral complementarity. This is the
conclusion shape of `Elasticity.ContactAndLubrication.complementarity_of_vi` with
`N = contactForce k f u` and the gap `contactGap x₀ u` of an obstacle at `x₀`, so the
frictionless scalar contact solution is admissible for every `0 ≤ μ`.
