# Valid perfect hash table

Let $T$ be a two-level perfect hash table with primary hash $h$,
$b$ buckets, secondary table sizes $m_i$ and secondary hashes $g_i$. Then $T$ is valid when two
conditions hold. Placement: whenever slot $j$ of bucket $i$ holds a binding $(k, v)$, we have
$i = h(k) \bmod b$ and $j = g_i(k) \bmod m_i$. Injectivity: for every bucket $i$, if keys $k_1$
and $k_2$ both occur in bindings stored in bucket $i$ and $g_i(k_1) \bmod m_i = g_i(k_2) \bmod m_i$,
then $k_1 = k_2$.

The injectivity condition follows from placement. It is recorded separately because choosing
secondary hash functions that are injective on each bucket's keys is the task of the FKS
construction.
