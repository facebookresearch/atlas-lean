# Visit probabilities across a cut of an admixture graph sum to one

Let `X` be a node of an [admixture graph](../admixture-graphs/admixture-graph.md) with root `ρ`, and
let `S` be a finite set of nodes that is an antichain for the ancestor relation (no element of `S`
is a proper ancestor of another) and that meets every root-ward chain from `X` (every sequence
`X = v₀, v₁, …, v_k = ρ` with each `v_(i+1)` a parent of `v_i` contains an element of `S`). Then the
[visit probabilities](../admixture-graphs/visit.md) across this cut sum to one:
`∑ c ∈ S, v(X, c) = 1`, where `v(X, c)` is the probability that the lineage of `X` passes through
`c`. This is the [cut lemma](sum-visit-eq-one-of-is-antichain-of-sepa.md) for the parents and
admixture proportions of the graph.
