# Average lookup cost of an absent key

Let $(h_i)_{i \in s}$ be a universal family of hash functions from keys to $\{0, \dots, m - 1\}$, indexed by a finite nonempty set $s$ (so $m > 0$), and for each $i \in s$ let $T_i$ be a hash table that hashes with $h_i$, has exactly $m$ buckets, stores every binding in its canonical bucket, and has key set $S$. For a key $k \notin S$, the scan-event counts of looking up $k$ satisfy

$$m \sum_{i \in s} \mathrm{time}(\mathrm{lookup}(k, T_i)) \le |s| \bigl(m + |S|\bigr),$$

that is, on average over $s$ at most one terminal event plus the load factor $|S|/m$.
