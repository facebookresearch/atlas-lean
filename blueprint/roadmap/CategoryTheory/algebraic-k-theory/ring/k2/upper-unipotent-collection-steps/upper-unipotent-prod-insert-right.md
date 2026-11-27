# Upper Unipotent Prod insert right

Right insertion for ordered upper-unipotent products: for `i ≠ j`,
`i < j`, `j < n`, right-multiplying `upperUnipotentProd n c` by
`x i j hij a` recollects to `upperUnipotentProd n c'` for an updated
coefficient assignment `c'` that agrees with `c` off
`orderedPositiveRoots n`. The Chevalley correction at each later column
lands in that same column and is absorbed locally; earlier columns are
handled by rank induction. Purpose: atomic right-insertion collection
step toward ordered upper-unipotent words. Nonclaims: no collection
termination, multiplication/inversion closure, ordered normal form,
coefficient or evaluator uniqueness, `toStableE` injectivity, TWT/Bruhat
statement, kernel generation, or Matsumoto claim.
