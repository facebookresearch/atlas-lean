# Fed-batch bioreactor balances

The volume `V`, substrate concentration `S` and biomass
concentration `X` solve the fed-batch balances on a set `I` of times, for a specific growth rate
`μ : ℝ → ℝ`, feed substrate concentration `Sin`, yield `Y` and feed rate `F : ℝ → ℝ`, if at every
`t ∈ I`, with derivatives within `I`,

`V' = F`,   `S' = (F / V) (Sin - S) - μ(S) X / Y`,   `X' = μ(S) X - (F / V) X`

(a quotient by `0` is `0`). Monod growth is `μ = mmRate μm Ks`, `μ(S) = μm S / (Ks + S)`.
