# Binary-search loop invariant

For an array `xs` of natural numbers and a natural-number key, a state `s` satisfies the binary-search invariant when `s lo ≤ s hi ≤ xs.size` and the reference lower-bound search restricted to the interval `[s lo, s hi)` returns the same index as the reference search `lowerBound xs key` on the full array. The program establishes this at loop entry; it is not assumed.
