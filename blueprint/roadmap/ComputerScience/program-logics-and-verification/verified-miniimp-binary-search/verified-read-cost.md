# Verified read cost of binary search

For every array `xs` sorted in nondecreasing order, every key and every
initial state `s`, running the binary-search program with fuel `xs.size + 7`
succeeds in a state `t` such that: the run is a read-counting big-step
execution; its read count equals the comparison count of the reference
lower-bound search `lowerBound xs key` and is at most `⌈log₂ (xs.size + 1)⌉`;
the weakest precondition and the Hoare triple with precondition `True` both
guarantee that the final `lo` equals the result of the reference lower-bound
search `lowerBound xs key`; and `t lo` satisfies the lower-bound specification
(`t lo ≤ xs.size`, every earlier element is less than the key, every later
element is at least the key).
