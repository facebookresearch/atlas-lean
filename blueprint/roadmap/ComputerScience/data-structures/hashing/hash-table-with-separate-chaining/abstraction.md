# Finite map represented by a hash table

The finite map represented by a hash table with
$m$ buckets is built from the list of all bindings of buckets $0, 1, \dots, m - 1$, concatenated
in this order: it binds exactly the keys occurring in this list, and binds each such key to the
value of its first binding in the list.
