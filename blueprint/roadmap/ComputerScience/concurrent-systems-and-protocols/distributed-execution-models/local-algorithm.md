# Algorithm in the LOCAL model

An algorithm with inputs in `I`, states in `S`, messages in
`M` and outputs in `O`, the same at every node. A node with identifier `i` and input `x` starts in
state `init i x`; in each round a node in state `s` sends the message `send s j` to its neighbour
with identifier `j`, and then moves to the state `update s m`, where `m` is the multiset of
messages its neighbours sent it; a node in state `s` outputs `out s`.

## Sources

- N. Linial, *Locality in distributed graph algorithms*, SIAM Journal on Computing 21(1), 1992, 193–201, §1.
