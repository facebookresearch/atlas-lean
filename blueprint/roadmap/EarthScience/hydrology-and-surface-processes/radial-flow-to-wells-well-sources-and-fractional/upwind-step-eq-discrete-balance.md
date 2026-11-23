# Conservative form

The upwind step is the finite-volume step with unit cell width and
time step `ν` for the face fluxes `f (Matrix.vecCons sIn s j)`: face `j` carries the fractional
flow of its left (upwind) state, the inflow state at the boundary face `0`.
