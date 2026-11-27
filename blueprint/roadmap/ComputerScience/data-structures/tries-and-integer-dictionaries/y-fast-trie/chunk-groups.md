# Chunking a list into groups

Given a bound $B$ and a list $l$ of $w$-bit keys, when
$B > 0$ the chunking of $l$ cuts $l$ from the left into consecutive chunks of exactly $B$
elements each, except that the last chunk holds the remaining one to $B$ elements; there are no
chunks when $l$ is empty. When $B = 0$, the chunking has no chunks if $l$ is empty and is the
single chunk $l$ otherwise.

So every chunk has at most $B$ elements when $B > 0$, but not when $B = 0$ and $l$ is
nonempty.
