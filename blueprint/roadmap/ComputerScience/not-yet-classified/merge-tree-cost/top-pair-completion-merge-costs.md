# Top Pair Completion Merge Costs

The chronological internal-node costs paid by Algorithm 2's final loop.

The recursive definition of `topPairCompletionCost` is written from the
oldest root outward; execution merges the newest pair first, so the current
whole-forest cost is appended after the recursive suffix schedule.
