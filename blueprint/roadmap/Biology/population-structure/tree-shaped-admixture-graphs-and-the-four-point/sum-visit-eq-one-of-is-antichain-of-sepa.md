# Cut lemma for lineage visit probabilities

Let `V` be a set of nodes with a designated root. Let each node `X` have a finite set `parents(X)`
of parents, of any size, with a well-founded parent relation (there is no infinite sequence
`X₀, X₁, …` with each `X_(i+1)` a parent of `X_i`), and let `prop(X, Y)` be real numbers, with no
sign condition, such that `∑ Y ∈ parents(X), prop(X, Y) = 1` for every node `X` other than the root.
Let `visit(X, c)` be any real function satisfying the first-step equation of the probability that
the lineage of `X`, traced toward the root, passes through `c`: `visit(X, c) = 1` if `X = c`, and
`visit(X, c) = ∑ Y ∈ parents(X), prop(X, Y) visit(Y, c)` otherwise.

Let `S` be a finite set of nodes that is an antichain for the ancestor relation (no element of `S`
is a proper ancestor of another) and that separates `X` from the root (every sequence
`X = v₀, v₁, …, v_k = root` with each `v_(i+1)` a parent of `v_i` contains an element of `S`). Then
`∑ c ∈ S, visit(X, c) = 1`.
