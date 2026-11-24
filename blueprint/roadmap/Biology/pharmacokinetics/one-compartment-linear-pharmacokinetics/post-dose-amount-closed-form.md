# Post-dose closed form for the periodic trajectory

The
amount just after dose `n` is
`exp (-k * tau)^n * D + D * ∑ j ∈ range n, exp (-k * tau)^j`,
derived from `post_dose_amount_succ` through the affine-recurrence
closed form.
