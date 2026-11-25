# Conservative mass update

On cells of a common width `Δx`, the
mass component of the update is the finite-volume step
`h i + Δt * discreteBalance Δx (faceMassFlux …) i` with one mass flux
per face, for every state and every numerical flux.
