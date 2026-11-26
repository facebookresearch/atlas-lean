# Total-order broadcast is equivalent to consensus

In asynchronous crash-prone message passing, a total-order (atomic) broadcast algorithm yields consensus by having every process broadcast its input and decide the first delivered value; conversely, a sequence of consensus instances, one per delivery slot on batches of received messages, yields total-order broadcast. Consequently total-order broadcast tolerating even one crash is impossible deterministically in the asynchronous model for at least two processes, whereas causal broadcast is solvable with any number of crashes.

## Proof sketch

Uniform total order makes the first delivered message the same at all processes, which gives agreement and validity; termination follows from validity of broadcast. For the converse, consensus on canonical batches orders all messages identically. The FLP impossibility transfers through the first reduction.

## Depends on

- [Broadcast abstractions](../broadcast-abstractions.md)
- [Causal broadcast with vector timestamps](../causal-broadcast-with-vector-timestamps.md)

## Proof depends on

- [FLP impossibility of asynchronous consensus with agreement, validity and termination](../../flp-impossibility/flp-impossibility.md)

## Sources

- Vassos Hadzilacos and Sam Toueg, "A Modular Approach to Fault-Tolerant Broadcasts and Related Problems", Department of Computer Science, Cornell University, 1994.
- Tushar Deepak Chandra and Sam Toueg, "Unreliable Failure Detectors for Reliable Distributed Systems", Journal of the ACM, 1996.
