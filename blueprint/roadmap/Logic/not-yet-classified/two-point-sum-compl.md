# Equivalence isolating two distinct points and their complement

Let `α` have decidable
equality and `a,b∈α` satisfy `a≠b`. `twoPointSumCompl a b` maps `inl 0` to `a`, `inl 1` to
`b`, and `inr x` to the underlying complement element `x`. Its inverse tests equality with
`a,b` and otherwise returns the complement summand.
