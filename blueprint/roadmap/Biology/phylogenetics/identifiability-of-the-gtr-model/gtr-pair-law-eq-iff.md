# GTR identifiability from a single branch, up to rate/time scaling

Let `(π, s)` and
`(π', s')` lie in the GTR domain and `t, t' > 0` be branch lengths. Their pair-site laws agree
if and only if `π = π'` and the branch-scaled exchangeabilities agree off the diagonal,
`t * s i j = t' * s' i j`. Thus one branch identifies the base frequencies and the products
`t * s i j`, and nothing more: the only permitted symmetries are the rate/time scaling
`(c • s, t) ~ (s, c * t)` (`gtrPairLaw_smul`) and the unused diagonal of `s`. This is a statement
about the law; it says nothing about estimators.
