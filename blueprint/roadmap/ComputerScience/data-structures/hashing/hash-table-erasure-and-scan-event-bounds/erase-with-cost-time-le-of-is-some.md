# Erase With Cost time le of is Some

For a hash table with $m$ buckets and hash function $h$, the selected chain of a key $k$ is the bucket at index $h(k) \bmod m$; keys need not lie in their selected bucket unless the table is valid. If looking up $k$ succeeds, then [erasing $k$](erase-with-cost.md) costs at most $n$ scan events, where $n$ is the length of the chain at bucket $h(k) \bmod m$. The hypothesis is that the lookup succeeds, not merely that $k$ occurs somewhere in the table.
