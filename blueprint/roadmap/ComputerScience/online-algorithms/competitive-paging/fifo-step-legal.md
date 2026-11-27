# One FIFO step keeps the cache legal

If a list $c$ of pages has no duplicates and at most
$k$ entries, then for every page $p$ the cache produced from $c$ by one FIFO step with capacity
$k$ on request $p$ also has no duplicates and at most $k$ entries.
