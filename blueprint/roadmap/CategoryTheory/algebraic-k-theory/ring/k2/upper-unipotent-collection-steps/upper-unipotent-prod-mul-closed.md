# Upper Unipotent Prod mul closed

Multiplication closure for ordered upper-unipotent products: the
head-left product `upperUnipotentProd n c₁ * upperUnipotentProd n c₂`
recollects to `upperUnipotentProd n c'` for an updated coefficient
assignment `c'` that agrees with the left assignment `c₁` off
`orderedPositiveRoots n`. The `m = n` specialization of `mul_prefix_absorb`,
which inducts on the right rank with `upperUnipotentProd_succ` and absorbs
each successor column by `mul_col_absorb`. Purpose: ordered-evaluator
multiplication closure step toward ordered upper-unipotent words.
Nonclaims: no inversion closure, collection termination, ordered
normal-form existence/uniqueness, coefficient/evaluator uniqueness beyond
the stated preservation, `toStableE` injectivity, TWT/Bruhat statement,
kernel generation, or Matsumoto claim.
