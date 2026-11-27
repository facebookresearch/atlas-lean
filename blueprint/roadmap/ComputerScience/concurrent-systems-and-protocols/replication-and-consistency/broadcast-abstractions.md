# Broadcast abstractions

In a system of processes subject to crash faults, a broadcast abstraction offers $\mathrm{broadcast}(m)$ and a $\mathrm{deliver}(m)$ event. *Best-effort broadcast* requires validity (if a correct process broadcasts $m$, every correct process eventually delivers $m$), no duplication and no creation (every delivered message was broadcast). *Reliable broadcast* adds agreement: if a correct process delivers $m$, every correct process eventually delivers $m$; *uniform* reliable broadcast requires this whenever any process, correct or not, delivers $m$. Messages are assumed unique, for instance identified by sender and sequence number. *FIFO*, *causal* and *total-order* broadcast add, respectively, that messages from one sender are delivered in sending order, that a message is delivered only after all messages that causally precede its broadcast, and that any two correct processes deliver the messages they both deliver in the same order; *uniform* total order requires this for any two processes.

## Depends on

- [Happened-before](../lamport-clocks/happens-before.md)

## Expansion

This page becomes ready once:

- Unresolved prerequisite named by review: crash-fault execution model with correct/faulty processes (statement prerequisite; not yet stated)

## Sources

- C. Cachin, R. Guerraoui and L. Rodrigues, *Introduction to Reliable and Secure Distributed Programming*, 2nd ed., Springer, 2011
- J. Aspnes, *Notes on Theory of Distributed Systems*, Yale University, 2020, <https://arxiv.org/abs/2001.04235>
