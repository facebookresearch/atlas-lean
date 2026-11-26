# Execution in the LOCAL model

`A.stateAfter G ids x k v` is the state of the node `v`
after `k` synchronous rounds of the algorithm `A` on the graph `G`, where the node `u` has
identifier `ids u` and input `x u`. After `0` rounds the node `v` is in state
`A.init (ids v) (x v)`. If after `k` rounds every node `u` is in state `s u`, then after `k + 1`
rounds the node `v` is in state `A.update (s v) m`, where `m` is the multiset of the messages
`A.send (s u) (ids v)` over the neighbours `u` of `v`.

## Sources

- N. Linial, *Locality in distributed graph algorithms*, SIAM Journal on Computing 21(1), 1992, 193–201, §1.
