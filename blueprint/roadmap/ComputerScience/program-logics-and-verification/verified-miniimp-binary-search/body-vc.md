# Verification condition of the binary-search loop body

For an array `xs` of natural numbers and a natural-number key, if a state `s` satisfies the binary-search invariant and the loop guard `lo < hi`, then `s` satisfies the generated sufficient precondition `wp` of the loop body for the invariant: the body's array read is in bounds and the invariant holds afterwards. The generator `wp` is sufficient for partial correctness, not claimed weakest: a loop whose annotation is `False` and whose guard is false terminates and satisfies `True`, yet its generated precondition is false.
