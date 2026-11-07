# Search fails exactly when no represented node has the target payload

If a node pool
represents, from the head $h$, the list of distinct identities $\ell$, then for every target
payload $t$ the search for $t$ from $h$ returns nothing if and only if no identity in $\ell$ has
a cell holding a node with payload $t$.
