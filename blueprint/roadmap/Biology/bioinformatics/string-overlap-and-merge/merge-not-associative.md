# Merging is not associative

[Merging](merge.md) along the overlap is not associative in general: over the natural numbers, $\mathrm{merge}(\mathrm{merge}([1], [2]), [1, 2]) = [1, 2]$, while $\mathrm{merge}([1], \mathrm{merge}([2], [1, 2])) = [1, 2, 1, 2]$. This is a specific counterexample; over a one-letter alphabet, merging returns the longer of its two inputs and is associative.
