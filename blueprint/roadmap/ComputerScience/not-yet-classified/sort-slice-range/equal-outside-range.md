# Equal Outside Range

`before` and `after` have the same extent and every half-open range
disjoint from `[start, start + count)` has exactly the same whole entries.

The quantified-range formulation is intentionally compositional: callers can
specialize it directly to the unconsumed suffix, while cell-level proofs may
establish it from their own pointwise write-frame lemmas.
