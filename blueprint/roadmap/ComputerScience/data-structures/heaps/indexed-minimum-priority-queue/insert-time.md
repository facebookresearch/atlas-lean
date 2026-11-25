# Logarithmic event bound for indexed-queue insertion

Let $W$ be a linearly ordered type
and let $W \cup \{\top\}$ be $W$ with a new greatest element $\top$ adjoined. Let $q$ be an
indexed minimum queue over the identities $0, \dots, n-1$ with keys in $W \cup \{\top\}$ whose
heap has $s$ entries, let $v < n$ be an identity and let $k \in W \cup \{\top\}$ be a key. For
each of the five counted events (comparisons, swaps, position reads, position writes, and entry
appends, pops or replacements), the number of times that event occurs when inserting $v$ with
key $k$ into $q$ is at most $20 (\lfloor \log_2 (s + 1) \rfloor + 1)$.
