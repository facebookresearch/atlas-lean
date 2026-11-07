# Placement invariant of a cuckoo hash table

A cuckoo hash table with hash functions
$h_1, h_2$ satisfies the placement invariant when every pair $(k, v)$ in slot $i$ of the first
table has $i = h_1(k)$, and every pair $(k, v)$ in slot $i$ of the second table has
$i = h_2(k)$.

This is what lets lookup check only two slots.
