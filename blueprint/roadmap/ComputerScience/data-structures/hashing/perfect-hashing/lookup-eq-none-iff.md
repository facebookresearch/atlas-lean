# Lookup fails exactly on unstored keys

For a valid two-level perfect hash table and
any key $k$, looking up $k$ returns no value if and only if there is no value $v$ such that the
binding $(k, v)$ is held in some slot of the table.
