# Verification condition of the binary-search program

For every array `xs` of natural numbers, natural-number key and entry state `s`, the generated sufficient precondition `wp` of the full binary-search program, with the loop annotated by the binary-search invariant (`lo ≤ hi ≤ xs.size` and equality of the reference indices on `[lo, hi)` and on the full array), holds at `s` for the postcondition `t lo = (lowerBound xs key).ret`: the final `lo` is the index returned by the reference lower-bound search.
