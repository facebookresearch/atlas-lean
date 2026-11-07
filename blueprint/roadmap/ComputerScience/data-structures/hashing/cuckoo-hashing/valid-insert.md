# Cuckoo insertion preserves the placement invariant

Let $T$ be a cuckoo hash table that
satisfies the placement invariant. If inserting the binding $k \mapsto v$ into $T$ (which
replaces an existing binding for $k$ in place) with some fuel bound succeeds and returns the
table $T'$, then $T'$ satisfies the placement invariant.
