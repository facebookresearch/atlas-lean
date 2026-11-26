# Simulating the first round with relation input servers

Consider an $R$-round reporting protocol with $R\geq1$ for $k>0$ relations. Section 2.4 of Beame, Koutris and Suciu groups the workers by relation: the first $p/k$ workers hold pieces of the first relation, the next $p/k$ hold pieces of the second, and so on. Correctness for every legal placement includes correctness for this one **if it is legal**.

For the [raw-position convention](raw-position-communication.md), the following is a restricted comparison. On the public shapes and positive worker counts under consideration, assume $k$ divides $p$ and fix such a grouped, balanced wiring of the actual positions. Each group's initial shards are then computable from its relation alone. Use the same input bit size and measurable randomized protocols in both conventions. A further **packing hypothesis**, not a property of arbitrary first-round messages, is required: one fixed relation-local encoder and recipient decoder must satisfy the following on every valid input and every draw on which the original first barrier fits.

- Using only its own relation, public parameters and the common seed, each input server computes its group's original first-round sends and packs a word for each recipient. The recipient's retained initial shard, as well as its incoming messages, must be recoverable.
- Each worker can reconstruct its original first post-barrier view from its packets, public parameters and the shared seed alone, including message boundaries and sender identities. At each recipient the sum of these packet lengths fits $C'M/p^{1-\varepsilon}$ with a constant uniform in the inputs and worker counts considered.

Under these hypotheses the input-server protocol can compute the same query on those parameters with the same round count, exponent and failure tolerance. The input servers produce the packets simultaneously in round one, then retire. Each recipient reconstructs its original view and executes the remaining worker rounds. A cap constant covering both the packing bound and the distributed protocol's bound preserves every originally successful draw. A lower bound for separate inputs therefore transfers to distributed inputs **where the hypotheses hold**.

They need not hold for the exact all-count cap. For a one-bit membership query with $\varepsilon=0$, fix any $C>0$ and choose $p>C$. The integer cap is zero. In the distributed convention the worker holding the raw bit can report membership locally with no sends. In the separate convention, [every completed run has empty initial worker words and all-empty inboxes](separate-zero-cap.md). For a fixed seed the completed reports cannot distinguish the two bit values; abort is failure, not a second answer. Thus the two success events are disjoint, so both inputs cannot have success probability greater than $1/2$. This obstruction concerns the concrete bit representation and unrestricted worker counts, not the asymptotic bounds in the paper.

## Depends on

- [Query reporting with public raw-bit layouts](raw-position-communication.md)

## Sources

- Paul Beame, Paraschos Koutris and Dan Suciu, *Communication Steps for Parallel Query Processing*, PODS 2013, §2.4, grouped initial distribution argument. The packing conditions and zero-cap example above concern the raw-position representation. [Authors' copy](https://homes.cs.washington.edu/~beame/papers/mpcpods.pdf).
