# Face Enthalpy Flux

Enthalpy flux through face `j`: the signed mass flux `Fm j` times the specific enthalpy
`specificEnthalpy (ef j) (pf j) (ρf j)` of the fluid crossing the face (flow work counted once,
inside the enthalpy). The face densities are positive (`_hρf`): at `ρ = 0` Lean's `x / 0 = 0`
would turn the enthalpy into `e` and drop the flow work.
