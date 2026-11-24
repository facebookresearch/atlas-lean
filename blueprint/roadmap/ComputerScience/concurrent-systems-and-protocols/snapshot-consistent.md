# Consistency of the Chandy–Lamport snapshot

Consider messages, each sent by a process at some position of a global event order and received by another at a later position, a recording position $c_p$ for each process $p$, and the position at which each process receives the marker from each other process. Suppose that on every channel carrying a message the receiver records no later than it receives the marker, and that a message sent at or after its sender's recording position is received no earlier than the marker on its channel (FIFO channels, markers sent right after recording). Then the recorded cut has no orphan messages: a message received before its receiver's recording position was sent before its sender's recording position.

## Sources

- K. M. Chandy and L. Lamport, "Distributed snapshots: determining global states of distributed systems", *ACM Transactions on Computer Systems* 3 (1985).
