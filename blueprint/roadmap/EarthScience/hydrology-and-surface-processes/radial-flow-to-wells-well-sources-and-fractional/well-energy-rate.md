# Well Energy Rate

Well energy rate of cell `i`: the injection rate `qI i` at the injected specific enthalpy
`hI i`, minus the production rate `qP i` at the cell's own specific enthalpy
`specificEnthalpy (ec i) (pc i) (ρc i)`. The signed well mass rate of the cell is `qI i - qP i`,
and the produced enthalpy leaves at the same production rate `qP i`. The cell densities are
positive (`_hρc`), as the face densities of `faceEnthalpyFlux`.
