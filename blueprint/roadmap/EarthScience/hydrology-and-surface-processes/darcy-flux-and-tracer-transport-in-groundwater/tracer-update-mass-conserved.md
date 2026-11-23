# The two-cell periodic upwind update conserves tracer mass

Conservative periodic tracer update on two cells: for every real upwind weight `ν` and all real
concentrations `c₁`, `c₂`, the updated values `c₁' = (1 - ν) * c₁ + ν * c₂` and
`c₂' = (1 - ν) * c₂ + ν * c₁` conserve total mass: `c₁' + c₂' = c₁ + c₂`.
