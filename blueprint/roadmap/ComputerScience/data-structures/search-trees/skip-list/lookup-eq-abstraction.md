# Skip-list search agrees with bottom-level lookup

For every skip list and every key $k$,
the top-down skip-list lookup of $k$ returns the same result as looking up $k$ in the
bottom-level abstraction, the list of key-value pairs of all stored nodes in order: the value of
the first pair with key $k$, or no value if there is none.
