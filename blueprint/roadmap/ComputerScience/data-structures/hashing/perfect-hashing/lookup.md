# Lookup in a perfect hash table

To look up a key $k$ in a two-level perfect hash table with
$b$ buckets, primary hash $h$, secondary sizes $m_i$ and secondary hashes $h_i$, let
$i = h(k) \bmod b$. If $m_i = 0$, the lookup returns nothing. Otherwise it inspects the single slot
$h_i(k) \bmod m_i$ of the secondary table of bucket $i$: if that slot holds a binding $(k, v)$, the
lookup returns $v$; if the slot is empty or holds a binding with a different key, the lookup
returns nothing.
