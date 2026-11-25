# FIFO paging as an online pager

The online pager with capacity $k$ whose states are the
legal caches of capacity $k$ (lists of at most $k$ distinct pages, oldest first), whose initial
state is the empty cache, whose cache in a state is that list itself, and which serves a request
$p$ by one FIFO step with capacity $k$.
