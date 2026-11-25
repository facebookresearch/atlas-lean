# The CAP theorem

In the asynchronous network model with at least two nodes, it is impossible to implement a read/write data object that guarantees both availability (every request received by a non-failing node eventually gets a response) and atomic consistency (linearizability) in all fair executions, including executions in which messages are lost. Moreover, it is impossible to implement a read/write data object that guarantees availability in all fair executions and atomic consistency in those fair executions in which no messages are lost.

## Depends on

- [Linearizability](../shared-memory-objects/linearizability.md)
- [Weak and strong fairness](../distributed-execution-models/weak-and-strong-fairness.md)
- [Asynchronous message-passing systems](../distributed-execution-models/asynchronous-message-passing-systems.md)

## Sources

- S. Gilbert and N. Lynch, "Brewer's conjecture and the feasibility of consistent, available, partition-tolerant web services", *ACM SIGACT News* 33(2):51–59, 2002, Theorem 1 and Corollary 1.1
