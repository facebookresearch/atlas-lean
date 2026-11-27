# Serve

For a handler $f$, a key $k$ and a hash table $T$, serving $k$ looks up $k$ in $T$: on a hit with value $v$ it returns $v$ and leaves $T$ unchanged; on a miss it returns $f(k)$ and the table obtained by inserting $k \mapsto f(k)$ into $T$.
