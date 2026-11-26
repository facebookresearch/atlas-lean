# Verified read cost of binary search

For every array `xs` of natural numbers sorted in nondecreasing order, every natural-number key and every initial state `s`, with fuel `xs.size + 7`, the read-counting interpreter and the ordinary interpreter of the binary-search program both succeed with the same final state `t`, and:

- the run is a read-counting big-step execution, and its read count equals the comparison count of the reference lower-bound search `lowerBound xs key` and is at most `⌈log₂ (xs.size + 1)⌉`;
- the generated sufficient precondition `wp` of the program for the postcondition "final `lo` equals the index returned by `lowerBound xs key`" holds at `s`;
- the partial-correctness Hoare triple with precondition `True` and that postcondition holds: from any initial state, every terminating execution of the program ends with `lo` equal to the index returned by `lowerBound xs key`;
- `t lo ≤ xs.size`, `xs[j] < key` for every `j < t lo`, and `key ≤ xs[j]` for every `j` with `t lo ≤ j < xs.size`, which includes the returned index itself when it is in range.
