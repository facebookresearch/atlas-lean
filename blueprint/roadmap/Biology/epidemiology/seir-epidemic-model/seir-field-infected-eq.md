# The SEIR infected rates split as new infections minus transfers

For all real `β`, `σ`, `γ`, `N`, every time `t` and every state `(S, E, I, R)`, the components along
`E` and `I` of the [SEIR vector field](seir-field.md) are the
[new-infection rates](new-infections.md) at susceptible level `S` minus the
[transfer rates](transfers.md):

`ℱ₀(S; E, I) - 𝒱₀(E, I) = β S I / N - σ E`,   `ℱ₁(S; E, I) - 𝒱₁(E, I) = σ E - γ I`,

with `β S I / N` read as `0` when `N = 0`, in the field and in `ℱ` alike.
