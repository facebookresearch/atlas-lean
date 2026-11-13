# Soundness of indexed interval-tree search

The search of an indexed interval tree $T$ for
a query interval $q = [c, d]$ returns nothing when $c > d$, and otherwise returns the entry, if
any, found by the instrumented overlap search of $q$ in the root tree of $T$. For every indexed
interval tree $T$, every query interval $q$ and every entry $e$, if this search returns $e$, then
$e$ is one of the entries stored in the root tree of $T$ and the interval of $e$ overlaps $q$.

The representation invariant of $T$ is not needed.
