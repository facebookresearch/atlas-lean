# One-generation estimate

For `a < b ≤ N`, with `k = b + 1 - a`, the probability that `b`
lineages have `a` parents is `(b choose k) * altMergeSum b k` (a single `k`-merger) up to an
error of at most `((b choose k) + 1) b ^ 4 doubleMergeProb` (simultaneous mergers).
