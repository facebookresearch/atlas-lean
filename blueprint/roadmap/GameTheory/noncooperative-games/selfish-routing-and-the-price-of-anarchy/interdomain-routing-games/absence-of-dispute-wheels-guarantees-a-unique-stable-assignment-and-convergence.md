# Absence of dispute wheels guarantees a unique stable assignment and convergence

If a stable paths problem has no dispute wheel, then it has a unique stable path assignment, and routing dynamics in which nodes repeatedly best-respond to their neighbours' current paths converge to it. Conversely, the existence of two distinct stable assignments implies a dispute wheel. The BAD GADGET instance has no stable assignment, and the DISAGREE instance has two, each witnessed by a dispute wheel.

## Proof sketch

Without dispute wheels one can grow a set of nodes whose paths are fixed in every stable assignment, adding at each step a node whose best available path through fixed nodes cannot be beaten; if no node can be added, the blocking preferences trace a dispute wheel.

## Depends on

- [Stable paths problem and dispute wheels](stable-paths-problem-and-dispute-wheels.md)

## Sources

- Timothy G. Griffin, F. Bruce Shepherd and Gordon Wilfong, "The Stable Paths Problem and Interdomain Routing", IEEE/ACM Transactions on Networking, 2002.
- Joan Feigenbaum, Michael Schapira and Scott Shenker, "Distributed Algorithmic Mechanism Design", Algorithmic Game Theory, Cambridge University Press, 2007.
