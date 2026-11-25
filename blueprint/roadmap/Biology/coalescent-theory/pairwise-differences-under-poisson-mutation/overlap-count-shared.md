# Overlap of two paths through a shared gene

Let `h` be a [ranked labeled history](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md)
of a sample of `n` genes, let `u ≤ n - 1`, and let `a`, `b`, `c` be genes with `a ≠ b` and
`a ≠ c`. After the first `u` events of `h`, the number of lineages that separate both `{a, b}`
and `{a, c}` (their [overlap count](overlap-count.md)) is

`1[a, b apart] + 1[a, c apart] - 1[b, c apart]`,

where `1[x, y apart]` is `1` if `x` and `y` are in [different lineages](pair-apart.md) after
`u` events and `0` otherwise. The case `b = c` is allowed: `{b, c}` is then the single gene `b`,
which is never apart, and the count is `2 · 1[a, b apart]`.

Epoch by epoch, this is the tree identity
`ℓ(P_{ab} ∩ P_{ac}) = (ℓ(P_{ab}) + ℓ(P_{ac}) - ℓ(P_{bc})) / 2`, where `P_{xy}` is the path between
the genes `x` and `y` and `ℓ` is length. When `b = c`, `P_{bb}` is the path from `b` to itself,
of length `0`, not the set of [branches with exactly one gene](pair-path.md) of `{b}` below them,
which are all the branches ancestral to `b`.
