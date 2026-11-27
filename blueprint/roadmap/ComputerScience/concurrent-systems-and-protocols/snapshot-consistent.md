# Consistency of the Chandy–Lamport snapshot

Consider messages, each sent by some process at some position and received by some process at some position, where positions range over a linearly ordered set; the sender and receiver of a message may be the same process, and no order between a message's sending and receiving positions is assumed. Consider also a recording position $c_p$ for each process $p$, and for all processes $p$ and $q$ the position at which $q$ receives the marker from $p$. Suppose that on every channel carrying a message the receiver records no later than it receives the marker, and that a message sent at or after its sender's recording position is received no earlier than the marker on its channel (FIFO channels, markers sent right after recording). Then the recorded cut has no orphan messages: a message received before its receiver's recording position was sent before its sender's recording position.

## Sources

- K. M. Chandy and L. Lamport, "Distributed snapshots: determining global states of distributed systems", *ACM Transactions on Computer Systems* 3 (1985).
