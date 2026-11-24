# Insertion does not affect other keys

For every hash table $T$, all keys $k \ne k'$ and
every value $v$, looking up $k'$ in the table obtained by inserting $k$ with value $v$ into $T$
gives the same result as looking up $k'$ in $T$, also when $k$ and $k'$ lie in the same bucket.
