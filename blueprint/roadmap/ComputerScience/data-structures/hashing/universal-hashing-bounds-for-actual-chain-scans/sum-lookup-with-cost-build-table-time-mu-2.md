# Average lookup cost of a stored key in tables built from a list

Let $(h_i)_{i \in s}$ be a universal family of functions from keys to $\{0, \dots, m - 1\}$, indexed by a finite nonempty set $s$ (so $m > 0$, and for distinct keys $x \ne y$ at most $|s| / m$ indices $i \in s$ satisfy $h_i(x) = h_i(y)$). Let $L$ be a list of key-value entries, let $S$ be its set of distinct keys, and for each
$i \in s$ let $T_i$ be the table with $m$ buckets obtained by inserting the entries of $L$ in order
using $h_i$. Here $\mathrm{time}(\mathrm{lookup}(k, T))$ counts the scan events in the bucket selected for $k$: one event per inspected entry, plus one terminal event when the key is not found. Computing the hash, indexing the bucket and the internals of key comparison are not charged; on an empty bucket an unsuccessful lookup costs one event, the empty-chain event. For a key $k \in S$,

$$m \sum_{i \in s} \mathrm{time}(\mathrm{lookup}(k, T_i)) \le |s| \bigl(m + (|S| - 1)\bigr).$$
