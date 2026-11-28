# Unary Amortized

The `Amortized` locale of `Amortized_Framework0.thy`: operations
act on a single state type, in a *sequence* starting from `init`.
Superseded by `AmortizedData` (which allows operations of arbitrary
arity and rose-tree histories), but still of interest because of its
simplicity — and it is the form closest to the book's presentation
(Ch. 19: a sequence of operations from an initial state, `Φ init = 0`).
Isabelle's `T` is real-valued here, as in that theory.
