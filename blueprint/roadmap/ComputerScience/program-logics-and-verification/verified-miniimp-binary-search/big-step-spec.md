# Specification of binary search on sorted arrays

For every array `xs` of natural numbers sorted in nondecreasing order, every natural-number
key and states `s`, `t`, if the MiniImp binary-search program evaluates from `s` to `t`, then `t lo ≤ xs.size`, every
element at an index below `t lo` is less than the key, and every element at an
index at least `t lo` is at least the key: `t lo` is the first index whose
value is at least the key, or the array size.
