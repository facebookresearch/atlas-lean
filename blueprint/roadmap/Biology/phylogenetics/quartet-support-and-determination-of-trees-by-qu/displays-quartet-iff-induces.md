# Displaying a quartet is inducing the family of its two pairs

Let `X` be a finite set of taxa. Let `T` be an
[unrooted binary phylogenetic tree](../../../Combinatorics/elementary-enumeration/counting-binary-phylogenetic-trees/unrooted-binary-tree.md)
on `X` and `x`, `y`, `z`, `w` taxa with `x ≠ z`, `x ≠ w`, `y ≠ z` and `y ≠ w`. Then `T`
[displays the quartet](../splits-compatibility-ultrametrics-and-upgma/displays-quartet.md) `xy | zw`
if and only if `T` [induces](induces.md) the family `{{x, y}, {z, w}}` on the set
`q = {x, y, z, w}`: some edge split `B` of `T` has `q ∩ B ∈ {{x, y}, {z, w}}`. The taxa `x` and `y`,
or `z` and `w`, may coincide. When the four taxa are distinct the family is the usual quartet
resolution of `q`; when `x = y` and `z = w` it is not one of the [resolutions](resolutions.md) of
`q`.
