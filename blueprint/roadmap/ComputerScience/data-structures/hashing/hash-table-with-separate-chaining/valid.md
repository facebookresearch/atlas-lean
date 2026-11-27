# Valid hash table

A hash table with hash function $h$ and $m$ buckets is valid when every
binding lies in its hash-selected bucket: for every bucket index $i < m$ and every key $k$, if
$k$ has a binding in bucket $i$, then $h(k) \bmod m = i$.

Keys within a single bucket are distinct automatically, since each bucket is an association list.
