# No protocol for $n$ generals tolerates $m$ traitors when $3 \le n \le 3m$

Suppose there
are at least two possible orders and the set of generals is finite with $n$ elements, where
$3 \le n \le 3m$. Then for every oral-message protocol, every commander $c$ and every number of
rounds $T$, the protocol does not solve the Byzantine generals problem with commander $c$ and at
most $m$ traitors in $T$ rounds: there are an order, a set of at most $m$ traitors and a
behaviour of the traitors for which the agreement condition (IC1) or the validity condition
(IC2) fails after $T$ rounds.

This is the theorem of Lamport, Shostak and Pease, proved by reduction to three generals.

**Model.** Synchronous rounds; at most $m$ Byzantine traitors; a complete network of reliable links with known senders; no signatures; deterministic protocols. The hypothesis $3 \le n$ is needed: with two generals there is a single lieutenant, and obeying the commander tolerates one traitor.

## Related topics

- [No synchronous protocol reaches Byzantine agreement when $3 \le n \le 3m$](../byzantine-agreement/not-solves-of-card-le-three-mul.md): the same bound for agreement with an input at every process, deduced from this one.

## Sources

- L. Lamport, R. Shostak, M. Pease, *The Byzantine Generals Problem*, ACM Transactions on Programming Languages and Systems 4(3), July 1982, 382–401: Section 2, the reduction of $3m$ or fewer generals to three ("Albanian generals"), pp. 385–386, and footnote 1 (three or more generals).
