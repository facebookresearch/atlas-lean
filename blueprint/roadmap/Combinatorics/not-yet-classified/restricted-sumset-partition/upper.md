# The known upper bound for Green's problem 25 can be lowered

There is a
`k : ℕ → ℕ` with `1 ≤ k N ≤ N` eventually, `k = o(N / log N)`, and
`¬ Property25 (k N) N` for all large `N`.

This is a restatement of `Green25.green_25.upper` of
`FormalConjectures/GreensOpenProblems/25.lean`: there the witness is an opaque
`green_25.upper.answer` left as `sorry`, here it is existentially quantified, and
the last conjunct is the (stronger over `atTop`) "eventually not" form. See the
module docstring for the exact comparison.
