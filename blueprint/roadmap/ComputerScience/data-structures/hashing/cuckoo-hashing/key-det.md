# Key determinism of a cuckoo hash table

A cuckoo hash table is key-deterministic when each
key is stored with at most one value: for every key $k$ and values $v_1, v_2$, if the bindings
$k \mapsto v_1$ and $k \mapsto v_2$ are both stored in the table, then $v_1 = v_2$. Duplicate
copies of the same pair are allowed.
