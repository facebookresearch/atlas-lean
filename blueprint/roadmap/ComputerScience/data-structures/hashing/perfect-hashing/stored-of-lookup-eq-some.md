# Soundness of perfect-hash lookup

For a two-level perfect hash table with decidable equality
on keys, and with no validity hypothesis, if looking up a key $k$ returns a value $v$, then some
secondary slot of the table holds the binding $(k, v)$.
