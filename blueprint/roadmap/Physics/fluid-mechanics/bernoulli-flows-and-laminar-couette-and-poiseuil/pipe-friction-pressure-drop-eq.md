# The Darcy-Weisbach loss of `PipeFrictionPorts`

For a duct of positive length `L`,
`ρ, μ, R > 0` and `G ≠ 0`, the loss coefficient `c = f L ρ / (2 D A²)` of the pipe (`D = 2 R`,
`A = π R²`) with the laminar Darcy factor `f = 64 / Re` gives the oriented pressure drop
`c Q |Q| = G L` at the flow rate `Q`, in both flow directions; the Fanning value `16 / Re` read as
a Darcy factor gives `G L / 4`. The factor `64 / Re` is the Darcy factor of the drop `G L`
(`pipe_darcyFactor_eq`), and the Darcy-Weisbach loss of that factor is the drop itself. At `G = 0`
there is no flow and `Re = 0`, and no friction factor is assigned.
