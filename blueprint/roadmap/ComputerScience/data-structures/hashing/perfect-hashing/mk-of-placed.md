# Placement suffices for validity of a perfect hash table

Let $T$ be a two-level perfect
hash table with $b$ buckets, primary hash $h$, secondary sizes $m_i$ and secondary hashes $h_i$.
If, whenever slot $j$ of the secondary table of bucket $i$ holds a binding $(k, v)$, we have
$h(k) \bmod b = i$ and $j = h_i(k) \bmod m_i$, then $T$ is valid.
