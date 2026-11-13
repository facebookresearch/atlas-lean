# Linear-scan overlap search

For a tree $T$ and a query interval $q$, the oracle search
returns the first entry, in the in-order list of entries of $T$, whose interval overlaps $q$ as
closed intervals, and returns nothing when no entry's interval overlaps $q$.

It is a separate full-traversal oracle used only by specifications and tests.
