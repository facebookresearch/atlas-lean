# Strict cost bound for nonempty insertion sequences

Starting from the empty dynamic
table and inserting the items of a nonempty array of length $k$ one at a time, the total cost
is less than $3k$.

The bound is strict because the first insertion, which allocates the first slot, has amortized
cost $2$ rather than $3$.
