# The graph-isomorphism Sigma protocol on Boolean adjacency functions

The **graph-isomorphism Sigma protocol** on the vertices `Fin n`. Statements are pairs of graphs
`(G₀, G₁)`, and the witnesses for `(G₀, G₁)` are the isomorphisms `φ` from `G₀` to `G₁`. The
prover's coins are a permutation `ρ` and its commitment is `graphAct ρ G₀`. The challenge is a bit
`b`, answered by `ρ⁻¹` if `b = false` and by `φ * ρ⁻¹` if `b = true`, and the verifier accepts the
answer `τ` to the commitment `H` when `graphAct τ H` is `G₀` or `G₁` according to `b`.
