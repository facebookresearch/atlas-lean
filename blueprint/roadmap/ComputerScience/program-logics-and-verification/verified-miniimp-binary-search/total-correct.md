# Total correctness of binary search

For every array `xs` of natural numbers sorted in nondecreasing order, every natural-number key and every
initial state `s`, the binary-search program run with fuel `xs.size + 7`
terminates in a state `t` that is also a big-step result, with `t lo ≤
xs.size`, `xs[j] < key` for every `j < t lo`, and `key ≤ xs[j]` for every
index `j ≥ t lo` of the array.
