# Parallel query communication

How can workers report a database query using only their local state and a bounded number of received bits? The model below fixes the public input shape and varies both the actual input and its placement. Its reporting guarantee is stated on a specified domain of worker counts and shapes.

- [Bit size of an encoded database](input-bits.md)
- [Legal initial placements for query communication](legal.md)
- [Balanced layouts exist for every positive worker count](nonempty.md)
- [Initial shards depend only on their wired positions](shard-congr.md)
- [Replaying local computation from a worker's inboxes](replay.md)
- [Local functions of a query communication protocol](protocol.md)
- [Maximum incoming bit load in a round](round-load.md)
- [Zero load means all messages are empty](round-load-eq-zero-iff.md)
- [Bit budget at a worker](receive-cap.md)
- [When a communication barrier completes](run-succ-eq-some-iff.md)
- [Completed separate-input runs at zero receive cap](separate-zero-cap.md)
- [Query reporting with public raw-bit layouts](raw-position-communication.md)
- [Gathering an encoded query input in one round](computes-one-round-full-load.md)
