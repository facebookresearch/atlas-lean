# Swapped Endpoint Flux balance fails

With the endpoint fluxes swapped (outflow at `x = 0`, inflow at `x = ℓ`), the balance
fails for the ramp on `[0, 1] × [0, 1/2]`: the true change is `-1/4`, the swapped
right-hand side is `+1/4`.
