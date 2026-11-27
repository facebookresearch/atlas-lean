# Each secondary table fits in the total secondary space

In a two-level perfect hash table
with $b$ buckets and secondary sizes $m_0, \dots, m_{b-1}$, every bucket $i < b$ satisfies
$m_i \le \sum_{j < b} m_j$, the total secondary space.
