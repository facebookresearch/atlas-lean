# The MSI snooping protocol maintains coherence

Consider cores with private write-back caches connected by a bus. All coherence requests are broadcast on the bus and snooped by every cache controller in one total order. The system has two atomicity properties:
- **atomic requests:** a request is ordered in the cycle it is issued;
- **atomic transactions:** no later request for the same block appears on the bus before the previous transaction completes.

In the MSI protocol each cache holds each block in one of three stable states:
- **Modified (M):** the only valid copy, readable and writable;
- **Shared (S):** a read-only copy;
- **Invalid (I):** no copy.

A load miss issues GetS and ends in S; loads in S or M and stores in M hit locally and issue no request; a store in I or S issues GetM and ends in M. Writing back a Modified block issues PutM, while an S copy may be evicted silently. When a controller snoops another core's GetS for a block it holds in M, it sends the current data both to the requester and to main memory, which is thereby updated, and moves to S. When it snoops another core's GetM, it moves to I from S or M, supplying the data from M.

Order all memory operations to a block in logical time as follows: bus transactions in bus order, and each local hit after the last bus transaction of its core for that block and before the next one, in the core's program order. A local hit happens while its core holds the block in S or M, so it falls inside the epoch begun by that core's last GetS or GetM. In this logical time the protocol maintains the [coherence invariants](cache-coherence-invariants.md):
- At most one cache holds a block in M, and then no other cache holds it in S.
- Every read returns the value of the last write in that order.

The total order matters. Even when a core's M copy briefly coexists in physical time with a stale S copy elsewhere, the invalidation is ordered before any read that could observe the new value.

## Depends on

- [Cache coherence invariants](cache-coherence-invariants.md)

## Sources

- D. J. Sorin, M. D. Hill and D. A. Wood, *A Primer on Memory Consistency and Cache Coherence*, Synthesis Lectures on Computer Architecture, Morgan & Claypool, 2011: Section 7.1 (snooping relies on a total order of coherence requests, with the sidebar example of Tables 7.3 and 7.4), and Section 7.2 (the baseline MSI snooping protocol, Figure 7.2 with its transitions, and the simple system model with atomic requests and atomic transactions of Section 7.2.2). The primer gives the correctness argument informally.
