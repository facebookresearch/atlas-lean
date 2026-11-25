# Lookup in a valid table returns exactly the stored binding

Let $T$ be a valid
open-addressing table, $k$ a key and $v$ a value. Then looking up $k$ in $T$ returns $v$ if and
only if the binding $k \mapsto v$ is stored in some slot of $T$.

Together with the fact that lookup after a successful insertion of $k \mapsto v$ returns $v$, this
says that a successful insertion really replaces the old binding: no other value for $k$ remains
stored afterwards.
