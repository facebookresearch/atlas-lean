# Under strict plurality the species tree maximizes quartet support

Let `X` be a finite set of taxa. Let `f q ρ` be real numbers, one for each set `q` of taxa and
family `ρ` of subsets, and let `S` be an
[unrooted binary phylogenetic tree](../../../Combinatorics/elementary-enumeration/counting-binary-phylogenetic-trees/unrooted-binary-tree.md)
on `X` for which `f` is a [strict plurality](is-strict-plurality.md): on every four-taxon set `q`,
the resolution that `S` induces is strictly more frequent under `f q` than each resolution of `q`
that `S` does not induce. Then every
[unrooted binary phylogenetic tree](../../../Combinatorics/elementary-enumeration/counting-binary-phylogenetic-trees/unrooted-binary-tree.md)
`T` on `X` has at most the support of `S`: `S_f(T) ≤ S_f(S)`, where `S_f` is the
[total quartet support](quartet-score.md) `S_f(T) = ∑_q f q (T|q)`.
