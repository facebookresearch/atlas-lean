# Well Cell Rate

Cell rate of a finite-volume chain with wells: the transport rate
`discreteBalance Δx F i = -(F (i + 1) - F i) / Δx` of cell `i` plus its well source `q i / Δx`.
`Δx > 0` is the common cell volume, `F j` the signed flux through face `j` and `q i` the signed
well rate of cell `i` (injection `q i > 0`, production `q i < 0`).
