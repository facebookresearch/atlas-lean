# Upper Unipotent Prod inv closed

Inverse re-collection for ordered upper-unipotent products:
`(upperUnipotentProd n c)⁻¹` equals `upperUnipotentProd n c'` for an updated
coefficient assignment `c'` that agrees with `c` off `orderedPositiveRoots n`.
The accepted inverse word is absorbed head-first: base coefficients vanishing
on the roots evaluate to `1`, and each reversed negated factor is a positive
root reinserted by `upperUnipotentProd_insert_right`. Holds over `[Ring R]`
with no import change. Purpose: ordered-evaluator inversion-closure step toward
ordered upper-unipotent words. Nonclaims: no collection termination, ordered
normal-form existence/uniqueness, coefficient/evaluator uniqueness beyond the
stated off-root preservation, `toStableE` injectivity, TWT/Bruhat statement,
kernel generation, or Matsumoto claim.
