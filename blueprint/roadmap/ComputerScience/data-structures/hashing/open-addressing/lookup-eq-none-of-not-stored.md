# Lookup of an absent key fails

Let $T$ be an open-addressing table and $k$ a key such that
no slot of $T$ stores a binding $k \mapsto v$ for any value $v$. Then looking up $k$ in $T$ returns
no value. No validity assumption on $T$ is needed.
