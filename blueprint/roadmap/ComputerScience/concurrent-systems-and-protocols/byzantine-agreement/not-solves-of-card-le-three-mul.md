# No synchronous protocol reaches Byzantine agreement when $3 \le n \le 3m$

Let there be at least two values and finitely many processes, $n$ of them, with $3 \le n \le 3m$. Then no deterministic synchronous protocol reaches Byzantine agreement with at most $m$ faulty processes, in any number of rounds: for every protocol and every number of rounds $T$ there are inputs, a set of at most $m$ faulty processes and a behaviour of the faulty processes for which agreement or validity fails after $T$ rounds.

**Model.** Synchronous rounds; Byzantine failures (a faulty process sends arbitrary messages, chosen independently for each recipient and each round); a complete network of reliable point-to-point links on which a receiver knows the sender; no signatures; deterministic protocols.

**Relation to the source.** This is the bound on the number of nodes in Theorem 1 of Fischer, Lynch and Merritt (1986), for the complete communication graph and for synchronous round-based protocols. Their theorem is stronger in two ways: it holds in a much more general model (their Locality and Fault axioms, which cover asynchronous systems and arbitrary communication graphs), and it also requires the connectivity of the communication graph to be at least $2m + 1$. The hypothesis $3 \le n$ follows their standing assumption that graphs have at least three nodes. The case $n = 2$ is [No synchronous protocol for two processes reaches Byzantine agreement with one fault](not-solves-of-card-eq-two.md); for $n = 1$ the bound fails, since a single process deciding its own input tolerates one fault. Fischer, Lynch and Merritt note that their impossibility results do not hold when the Fault axiom is weakened, for instance by unforgeable signatures (§2). For this problem signatures do not remove the whole range: with $n \le 2m$ agreement remains impossible even with signatures, since the processes split into two groups of at most $m$ with different inputs, and either group may be the faulty one behaving correctly, so validity forces each group to decide its own input in the same execution. Only the range $2m < n \le 3m$ becomes solvable: with the signed-message algorithm SM($m$) of Lamport, Shostak and Pease (§4, Theorem 2) every process can broadcast its input consistently, and the majority of the inputs received then satisfies agreement and validity. This paragraph combines the two sources; neither of them states it.

**Proof.** By reduction to the commander version: a protocol reaching Byzantine agreement yields, with one extra round in which the commander sends its order, a protocol solving the Byzantine generals problem, which is impossible for $3 \le n \le 3m$.

## Informally uses

- [Byzantine agreement yields the Byzantine generals problem](solves-to-oral.md): the reduction.
- [No protocol for $n$ generals tolerates $m$ traitors when $3 \le n \le 3m$](../byzantine-generals-problem/not-solves-of-card-le-three-mul.md): the commander version, proved by the hexagon argument of Fischer, Lynch and Merritt for three generals and the simulation argument of Lamport, Shostak and Pease for more.

## Background

- [The oral messages algorithm solves the Byzantine generals problem](../byzantine-generals-problem/byzantine-generals.md): with more than $3m$ generals the commander version is solvable, so $3m + 1$ processes are needed and suffice there.

## Sources

- M. J. Fischer, N. A. Lynch, M. Merritt, *Easy impossibility proofs for distributed consensus problems*, Distributed Computing 1(1), 1986, 26–39: §3, Theorem 1 and §3.1.
- L. Lamport, R. Shostak, M. Pease, *The Byzantine Generals Problem*, ACM TOPLAS 4(3), 1982, 382–401: §2.
