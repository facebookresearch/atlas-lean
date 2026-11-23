# Renewal input, nonlattice case

Cramér conditions on nonlattice i.i.d. scores, together
with the two inputs that renewal theory supplies and that are taken here as hypotheses: the
ladder decomposition of the maximal segment score (`ladder`) and the nonlattice renewal tail
`P(Y > t) ~ C e^{-θ t}` of the excursion heights (`tendsto_tail`). The fields `cramer` and
`nonlattice` record the setting in which renewal theory provides `ladder` and `tendsto_tail`;
the limit theorem uses only the latter two.

No instance of this structure (or of `LatticeRenewalInput`) is constructed here: that would
require deriving the ladder input from the scores. Non-vacuity is shown only for `LadderInput`,
in the test file.
