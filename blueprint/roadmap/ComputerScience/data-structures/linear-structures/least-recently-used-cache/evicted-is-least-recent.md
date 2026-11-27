# The evicted key is the least recently used one

Let $C$ be an LRU cache of capacity $c$,
let $k'$ be a key not stored in $C$, and let $k$ be a key stored in $C$. If $k$ is no longer
stored after putting $k'$ with any value $v$ into $C$, then $C$ held exactly $c$ entries and $k$
is the last key of $C$, that is, the least recently used one.
