# The effect of a primitive operation

The relation `Q ⇒_op Q'` of Harrison, Ruzzo and
Ullman: the primitive operation `op` turns the configuration `Q = (S, O, P)` into
`Q' = (S', O', P')`.

* `enter r into (s, o)` needs `s ∈ S` and `o ∈ O`; it adds `r` to `P[s, o]`.
* `delete r from (s, o)` needs `s ∈ S` and `o ∈ O`; it removes `r` from `P[s, o]`.
* `create subject s` needs `s ∉ O`; it adds `s` to `S` and to `O`, with an empty row and column.
* `create object o` needs `o ∉ O`; it adds `o` to `O`, with an empty column.
* `destroy subject s` needs `s ∈ S`; it removes `s` from `S` and from `O`.
* `destroy object o` needs `o ∈ O \ S`; it removes `o` from `O`.

Every other cell of `S' × O'` keeps its rights. An operation whose precondition fails yields no
configuration.
