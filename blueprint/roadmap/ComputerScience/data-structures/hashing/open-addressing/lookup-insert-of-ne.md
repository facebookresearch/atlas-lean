# Insertion does not affect lookups of other keys

Let $T$ be a valid open-addressing table and
suppose inserting the binding $k \mapsto v$ into $T$ succeeds with result $T'$. Then for every key
$k' \ne k$, looking up $k'$ in $T'$ gives the same result as looking up $k'$ in $T$.

Together with the fact that looking up $k$ in $T'$ returns $v$, this is the map-update
specification of insertion, matching the corresponding statement for separate chaining.
