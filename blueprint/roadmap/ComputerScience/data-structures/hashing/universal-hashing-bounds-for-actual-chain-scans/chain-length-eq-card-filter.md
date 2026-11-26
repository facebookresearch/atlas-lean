# Chain length eq card filter

For a valid hash table with $m > 0$ buckets, hash function $h$ and key inventory $S$, and any key $k$, the chain of the selected bucket $h(k) \bmod m$ has as many entries as there are keys $x \in S$ with $h(x) \bmod m = h(k) \bmod m$, including $k$ itself when $k \in S$. Keys with different raw hashes collide when their hashes agree modulo $m$.
