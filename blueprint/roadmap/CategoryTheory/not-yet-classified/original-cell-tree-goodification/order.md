# Order

The refining partial order the goodification puts on the same carrier `P`.

Refining deletes comparabilities: `p ≤ q` in this order implies `p ≤ q` in the
original order of `O` (`sameLabelOrder_below`), equivalently the identity
function on `P` is monotone from this order to the original one
(`sameLabelHom`, whose value at `p` is `p`). The converse implication is not
claimed, the two orders are not asserted equivalent, and this is not a freedom
to extend or refine a partial order arbitrarily.
