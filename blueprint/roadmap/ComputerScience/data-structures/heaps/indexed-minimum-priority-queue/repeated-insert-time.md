# Event bound for building an indexed queue by repeated insertion

Let $W$ be a linearly
ordered type and let $W \cup \{\top\}$ be $W$ with a new greatest element $\top$ adjoined. Let
$q_0, \dots, q_n$ be indexed minimum queues over the identities $0, \dots, n-1$ with keys in
$W \cup \{\top\}$, and let $k_0, \dots, k_{n-1}$ be keys in $W \cup \{\top\}$. Suppose $q_0$ is
the empty queue and, for each $i < n$, inserting identity $i$ with key $k_i$ into $q_i$ succeeds
and returns $q_{i+1}$. Then for each of the five counted events (comparisons, swaps, position
reads, position writes, and entry appends, pops or replacements), the total number of times that
event occurs over these $n$ insertions is at most $20 n (\lfloor \log_2 (n + 1) \rfloor + 1)$.
