# Feasible Assignment

An assignment of item indices to bins is feasible for `B` bins if
all item sizes lie in `[0, 1]`, every item is assigned to a bin below `B`,
and every bin's total size is at most `1`. Zero-size items are allowed.
Coverage is part of the definition: without it an assignment could send items to bins
outside the range, and the per-bin bound alone would hold vacuously.
