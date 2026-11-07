# Solution of the Kermack–McKendrick SIR system

`(S, I, R)` solves the Kermack–McKendrick SIR system with transmission rate `β`, removal
rate `γ` and population size `N` for all times `t ≥ 0`:
`S' = -β S I / N`, `I' = β S I / N - γ I`, `R' = γ I`.
