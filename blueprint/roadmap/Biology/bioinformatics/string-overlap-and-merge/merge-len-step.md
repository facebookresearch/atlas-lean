# Merge step tracking the length

One step of a fold that tracks a length beside the merged string: from a pair $(a, \ell)$ and a string $s$, the step returns $(\mathrm{merge}(a, s), \ell + |s| - \mathrm{overlap}(a, s))$, with truncated subtraction, where merge and overlap are those of the [merge along the overlap](merge.md).
