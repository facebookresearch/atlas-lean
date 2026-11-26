# Timed message-passing runs

Fix a finite set of processors on a complete network. A timed history records each processor's initial local state and, at each nonnegative integer clock tick, an ordered list of steps. A history is a legal timed run if each processor takes at most one step per tick and each receive takes a subset of that processor's pending messages. The subset and the list of steps at a tick may both be empty.

A send places a message in the recipient's buffer. Its address (clock tick and position within the tick) identifies the occurrence, so sends with identical payloads remain distinct. At a receive, the pending messages are exactly the earlier sends to that recipient not already delivered. The order within a tick is a convention: a receive can take an earlier send in the same tick but not a later one.

## Background

A [deterministic local protocol](protocol.md) fixes the initial state from the input and selects an instruction from the current state. At a receive it sees an unordered multiset of sender–payload pairs, not the occurrence addresses. [Conformance](conforms.md) compares the history with that protocol. In an infinite clock history, a [correct processor](correct.md) conforms and takes steps at arbitrarily late ticks. A send occurrence is [lost](lost.md) if its recipient receives at arbitrarily late ticks but never receives that occurrence. An infinite clock history can still contain only finitely many steps; finite-run correctness, decision outputs, and omission faults are separate notions.

The [communication bound](communication-bound.md) is conditional on a send at $s_1\in I$ and a receive by its recipient at $s_2\in I$ with $s_2\ge s_1+\Delta$: the occurrence must be delivered at or before $s_2$. With no such receive the bound imposes no delivery deadline. The [processor bound](processor-bound.md) requires each correct processor to step in each complete positive-length window $[t,t+\Phi)$ contained in $I$. Neither bound is a condition for a legal run.

## Sources

- C. Dwork, N. Lynch and L. Stockmeyer, "Consensus in the presence of partial synchrony", *Journal of the ACM* 35(2):288–323, 1988, Sections 2.1–2.3.
