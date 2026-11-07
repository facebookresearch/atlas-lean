# Stored values in a valid perfect hash table are unique

In a valid two-level perfect hash
table, if some secondary slots hold bindings $(k, v_1)$ and $(k, v_2)$ with the same key $k$, then
$v_1 = v_2$.

This is a direct consequence of placement (both bindings would occupy the one slot their shared
key hashes to), so it needs no decidable equality on keys.
