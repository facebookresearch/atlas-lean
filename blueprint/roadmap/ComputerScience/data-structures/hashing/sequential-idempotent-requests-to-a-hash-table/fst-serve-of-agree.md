# Fst serve of agree

A table agrees with a handler $f$ when every value returned by a lookup equals the handler's value: for all keys $k$ and values $v$, if looking up $k$ returns $v$ then $v = f(k)$. This is a condition on lookups, not on the represented finite map, since a key may occur in a bucket other than the one lookup selects. If $T$ agrees with $f$, then [serving](serve.md) any key $k$ returns $f(k)$.
