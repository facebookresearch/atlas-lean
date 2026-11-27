# FIFO keeps the cache legal on every request sequence

If a list $c$ of pages has no
duplicates and at most $k$ entries, then for every finite request sequence $\sigma$ the cache
obtained from $c$ by serving the requests of $\sigma$ in order, each with one FIFO step of
capacity $k$, also has no duplicates and at most $k$ entries.
