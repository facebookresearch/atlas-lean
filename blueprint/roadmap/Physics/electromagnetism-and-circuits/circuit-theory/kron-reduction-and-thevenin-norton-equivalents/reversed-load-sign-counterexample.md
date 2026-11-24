# With the load current reversed the divider formula fails

Under the wrong sign convention `K V = j_eff + I`, with `K = 1` and `j_eff = 1`, the load
`R_L = 2` admits the operating point `V = 2`, `I = 1`: it satisfies `V = 1 + I` and `V = 2 I`, but
`V` differs from the divider value `V_th R_L / (R_th + R_L) = 2/3` of the
[resistive-load formula](one-port-resistive-load.md).
