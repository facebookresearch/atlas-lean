# Equal support forces the same quartet trees under strict plurality

Let `X` be a finite set of taxa. Let `f q ρ` be real numbers, one for each set `q` of taxa and
family `ρ` of subsets, and let `S` be an
[unrooted binary phylogenetic tree](../../../Combinatorics/elementary-enumeration/counting-binary-phylogenetic-trees/unrooted-binary-tree.md)
on `X` for which `f` is a [strict plurality](is-strict-plurality.md): on every four-taxon set `q`,
the resolution that `S` induces is strictly more frequent under `f q` than each resolution of `q`
that `S` does not induce. If an
[unrooted binary phylogenetic tree](../../../Combinatorics/elementary-enumeration/counting-binary-phylogenetic-trees/unrooted-binary-tree.md)
`T` on `X` has the same [total quartet support](quartet-score.md) `S_f(T) = ∑_q f q (T|q)` as `S`,
`S_f(T) = S_f(S)`, then `T` and `S` induce the same resolutions: for every four-taxon set `q` and
every resolution `ρ` of `q`, `T` induces `ρ` if and only if `S` does.
