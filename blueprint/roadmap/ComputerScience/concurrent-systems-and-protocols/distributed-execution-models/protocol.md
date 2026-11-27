# Protocols of asynchronous message-passing systems

A protocol for the processes `P` on the
directed network `G` gives each process `i` a set `init i` of initial states and a deterministic
transition function `trans i`. It maps a state of `i` and a multiset of messages delivered to `i`,
each paired with its sender, to a new state of `i` and a multiset of messages to send, each paired
with its recipient, which is an out-neighbour of `i` in `G`.
