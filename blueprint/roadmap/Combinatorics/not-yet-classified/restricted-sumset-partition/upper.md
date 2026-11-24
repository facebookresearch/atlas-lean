# The known upper bound for Green's problem 25 can be lowered

There is a
`k : ℕ → ℕ` with `1 ≤ k N ≤ N` eventually, `k = o(N / log N)`, and
`¬ Property25 (k N) N` for all large `N`.

In `FormalConjectures/GreensOpenProblems/25.lean`, `green_25.upper` uses the fixed
opaque function `green_25.upper.answer`. Here the witness is existentially quantified,
and the last conjunct is the stronger "eventually not" condition at `atTop`.
See the module docstring for the exact comparison.
