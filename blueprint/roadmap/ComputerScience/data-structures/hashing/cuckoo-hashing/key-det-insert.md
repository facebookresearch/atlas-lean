# Cuckoo insertion preserves key determinism

Let $T$ be a cuckoo hash table that
satisfies the placement invariant and is key-deterministic. If inserting a key $k$ with value
$v$ into $T$ with some fuel succeeds with result $T'$, then $T'$ is key-deterministic. In
particular, replacement leaves no stale copy of $k$ with a different value in the other slot.
