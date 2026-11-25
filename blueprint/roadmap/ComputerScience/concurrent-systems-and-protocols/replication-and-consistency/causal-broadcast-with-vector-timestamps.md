# Causal broadcast with vector timestamps

Causal broadcast is [reliable broadcast](reliable-broadcast.md) with *causal delivery*: no process delivers a message $m'$ unless it has already delivered every message $m$ that causally precedes $m'$ ($m \to m'$). Here $m \to m'$ holds if the sender of $m'$ broadcast or delivered $m$ before broadcasting $m'$, and $\to$ is closed under transitivity.

**Algorithm.** Implement causal broadcast on top of reliable broadcast in an asynchronous system with reliable channels and crash failures. Each process $p$ keeps a vector $\mathit{VC}_p$, where $\mathit{VC}_p[q]$ counts the messages from $q$ that $p$ has delivered, all initially $0$. To broadcast $m$, process $p$ delivers $m$ to itself, reliably broadcasts $(\mathit{VC}_p, m)$, and then increments $\mathit{VC}_p[p]$. When $p$ receives $(V, m)$ from another process $q$, it adds the message to a pending set. Then, as long as some pending $(V', m')$ from some $r$ satisfies $\mathit{VC}_p \ge V'$ componentwise, $p$ removes it, delivers $m'$ and increments $\mathit{VC}_p[r]$.

**Correctness.**
- *Counting.* $\mathit{VC}_p[q]$ is always the number of messages from $q$ delivered at $p$, and the $k$-th message broadcast by $q$ carries $V[q] = k - 1$. Hence $p$ delivers the messages of each sender in the order they were sent: the $k$-th message from $q$ becomes deliverable only after the first $k - 1$ have been delivered.
- *Causal delivery.* Suppose a message $m$ with timestamp $V$ is delivered at $p$. Then $p$ has already delivered at least $V[r]$ messages from each process $r$. These include every message that the sender of $m$ had delivered or broadcast before $m$, and these are, by induction, all messages that causally precede $m$.
- *Termination.* Every message broadcast by a correct process is reliably delivered everywhere. By induction along the causal order, its delivery condition eventually holds at every correct process. So the reliable broadcast properties carry over, and deliveries respect causal order.

## Depends on

- [Reliable broadcast](reliable-broadcast.md)

## Background

- [Causal delivery of updates](causal-delivery-of-updates.md)
- [Happened-before](../lamport-clocks/happens-before.md)

## Sources

- A. Bieniusa, *Fault-tolerance in message-passing distributed systems: broadcast*, lecture slides, Programming Distributed Systems, TU Kaiserslautern, 2020, <https://pl.cs.uni-kl.de/homepage/teaching/ss20/progdist/slides/5_broadcast.pdf>: the specification of reliable causal broadcast (slide 41) and Algorithm 2 with vector clocks (slide 47, after Raynal, Schiper and Toueg). The correctness argument is given above.
- M. Raynal, A. Schiper and S. Toueg, "The causal ordering abstraction and a simple way to implement it", *Information Processing Letters* 39(6):343–350, 1991.
- K. Birman, A. Schiper and P. Stephenson, "Lightweight causal and atomic group multicast", *ACM Transactions on Computer Systems* 9(3):272–314, 1991.
