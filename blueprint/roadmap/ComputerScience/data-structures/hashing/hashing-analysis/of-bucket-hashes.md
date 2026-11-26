# Two-level layout with doubled square sizing

For a nonempty finite key set of size $n$,
a value for each key, a primary hash into $n$ buckets, and a natural-valued secondary hash per
bucket, allocate $2k^2$ slots for a bucket assigned $k$ keys. A slot holds a binding chosen
from the keys assigned to that bucket whose secondary hash reduces to that slot modulo the
bucket's capacity; a slot with no such key is vacant. In particular an empty bucket has no
secondary slots. The choice describes the table, not an implementation of its construction.
