# Under strict plurality other topologies have smaller support

Let `X` be a finite nonempty set of taxa. Let `f q ρ` be real numbers, one for each set `q` of taxa
and family `ρ` of subsets, and let `S` be an
[unrooted binary phylogenetic tree](../../../Combinatorics/elementary-enumeration/counting-binary-phylogenetic-trees/unrooted-binary-tree.md)
on `X` for which `f` is a [strict plurality](is-strict-plurality.md): on every four-taxon set `q`,
the resolution that `S` induces is strictly more frequent under `f q` than each resolution of `q`
that `S` does not induce. Then every
[unrooted binary phylogenetic tree](../../../Combinatorics/elementary-enumeration/counting-binary-phylogenetic-trees/unrooted-binary-tree.md)
`T` on `X` that is not
[isomorphic](../../../Combinatorics/elementary-enumeration/counting-binary-phylogenetic-trees/iso.md)
to `S` has strictly smaller [total quartet support](quartet-score.md) `S_f(T) = ∑_q f q (T|q)`:
`S_f(T) < S_f(S)`. Equivalently, every unrooted binary tree `T` on `X` with `S_f(T) ≥ S_f(S)` is
isomorphic to `S`.
