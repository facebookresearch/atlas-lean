# The CAP theorem under partial synchrony

In the partially synchronous network model of Gilbert and Lynch, in which every node has a clock and every message that is delivered arrives within a known bound (a different model from the eventual-synchrony model of Dwork, Lynch and Stockmeyer), it is still impossible to implement a read/write data object that guarantees availability and atomic consistency in all executions, including those in which messages are lost. Unlike the asynchronous case, it becomes possible when no messages are lost.

## Proof depends on

- [The CAP theorem](the-cap-theorem.md)

## Expansion

This page becomes ready once:

- Unresolved prerequisite named by review: Gilbert–Lynch partially synchronous model and bridge (statement prerequisite; not yet stated)

## Sources

- S. Gilbert and N. Lynch, "Brewer's conjecture and the feasibility of consistent, available, partition-tolerant web services", *ACM SIGACT News* 33(2):51–59, 2002, Theorem 2
