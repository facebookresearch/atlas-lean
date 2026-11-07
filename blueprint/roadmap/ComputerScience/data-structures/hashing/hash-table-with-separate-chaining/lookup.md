# Hash table lookup

For a hash table with hash function $h$ and $m$ buckets, looking up
a key $k$ searches only the bucket with index $h(k) \bmod m$: the result is the value bound to
$k$ in that bucket's association list, or nothing if $k$ has no binding there.
