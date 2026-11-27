# Lookup With Cost cost le

For a hash table with $m$ buckets and hash function $h$, the selected chain of a key $k$ is the bucket at index $h(k) \bmod m$; keys need not lie in their selected bucket unless the table is valid. The [costed lookup](lookup-with-cost.md) of $k$ takes at most $1 + n$ scan events, where $n$ is the length of the selected chain.
