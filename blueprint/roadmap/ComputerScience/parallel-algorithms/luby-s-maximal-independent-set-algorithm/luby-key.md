# Luby Key

The key of vertex `v`: its priority, with the vertex index as tie-breaker. Keys compare
lexicographically by `(prio v, v)` (`lubyKey_lt_iff`).
