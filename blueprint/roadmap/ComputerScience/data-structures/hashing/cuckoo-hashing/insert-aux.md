# Cuckoo eviction loop

The eviction loop takes a cuckoo hash table with hash functions $h_1$
and $h_2$, a key–value pair $(k, v)$, a choice of the first or second table, and a natural
number as fuel, and either returns a table or fails. With fuel $0$ it fails. With fuel $n + 1$
and the first table chosen, it writes $(k, v)$ into slot $h_1(k)$ of the first table; if that
slot was empty it returns the resulting table, and otherwise it repeats on the resulting table
with the evicted pair, the second table and fuel $n$. With the second table chosen it does the
same at slot $h_2(k)$ of the second table and continues with the first table.
