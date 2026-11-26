# Configurations of an asynchronous message-passing system

A configuration of processes
`P` with states in `Q`, exchanging messages in `M`, gives the state `state i` of every process `i`
and, for every ordered pair of processes `i, j`, the channel `chan i j`: the multiset of messages
sent from `i` to `j` and not yet delivered.
