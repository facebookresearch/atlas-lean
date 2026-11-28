# Cell rate of a finite-volume chain with wells

On a chain of `n` cells of common positive volume `Δx > 0` (per unit cross-section), cell `i`
lying between the faces `i` and `i + 1`, let `F 0, …, F n` be the signed fluxes through the faces,
positive towards increasing index, and `q i` the signed well rate of cell `i` (injection
`q i > 0`, production `q i < 0`). The rate of cell `i` is the transport rate
`-(F (i + 1) - F i) / Δx` plus the well source `q i / Δx`.
