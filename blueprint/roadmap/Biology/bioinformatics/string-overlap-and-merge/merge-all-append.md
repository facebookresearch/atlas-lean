# Merge All append

Regrouping coherence of the fold along a fixed ordering: merging along
`l₁ ++ l₂` equals folding `l₂` onto the merge of `l₁`. Binary `merge` itself
is not associative (see `merge_not_associative`); the well-defined object is
the fold along a fixed ordering.
