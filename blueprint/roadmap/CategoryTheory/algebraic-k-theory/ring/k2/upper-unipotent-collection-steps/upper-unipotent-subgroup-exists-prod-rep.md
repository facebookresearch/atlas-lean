# Upper Unipotent Subgroup exists prod repr

Subgroup representation: every `g ∈ upperUnipotentSubgroup n` equals
`upperUnipotentProd n c` for a coefficient assignment vanishing off
`orderedPositiveRoots n`. Proved by `Subgroup.closure_induction`: generator via
the zero-coefficient identity plus `upperUnipotentProd_insert_right`, one via
the zero function and `prod_one_of_zero_on_roots`, multiplication via
`upperUnipotentProd_mul_closed`, inversion via `upperUnipotentProd_inv_closed`,
normalizing each witness to zero off the roots. Purpose: ordered-evaluator
subgroup representation toward ordered upper-unipotent words. Nonclaims: no
range/subgroup equality, coefficient/evaluator uniqueness, injectivity,
normal-form uniqueness, TWT/Bruhat statement, kernel generation, or Matsumoto
claim.
