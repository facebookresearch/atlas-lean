# Indexed minimum queue

Let $W$ be a linearly ordered type, let $W \cup \{\top\}$ be $W$
with a new greatest element $\top$ adjoined, and let $n$ be a natural number. An indexed
minimum queue over the identities $0, \dots, n-1$ consists of a binary min-heap whose entries are
pairs $(k, v)$ of a key $k \in W \cup \{\top\}$ and an identity $v < n$, ordered lexicographically
(first by key, then by identity), together with a position vector assigning to each identity
$v < n$ either nothing or an index $i < n$. It is required that the heap has at most $n$ entries
and that, for all identities $v < n$ and indices $i < n$, the position of $v$ is $i$ exactly
when $i$ is a slot of the heap whose entry has identity $v$.
