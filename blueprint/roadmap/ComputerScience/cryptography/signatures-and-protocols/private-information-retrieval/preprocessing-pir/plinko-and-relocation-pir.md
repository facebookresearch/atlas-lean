# Updatable preprocessing PIR via invertible PRFs and relocation

(i) *Plinko:* built on the RMS24 single-server preprocessing PIR scheme (with a Piano-based variant in Appendix B), replacing linear hint search by an invertible pseudorandom function lets the client locate, in time $\tilde O(1)$, the hint slot that contains a queried index (the result of inversion agrees with a linear scan whenever the key is correct), and supports database updates by patching only the affected hint parities; correctness and privacy carry over. (ii) *Relocation data structure:* to achieve a tight space–time trade-off, Wang and Ren maintain a relocation graph on hint slots in which each consumed slot is relocated to a fresh one; the in-edge and out-edge lookups are exact (for a history without repetition, the out-edge of $u$ is $v$ iff there is a directed edge from $u$ to $v$), so the client can follow relocation chains, and, assuming one-way functions (which give the pseudorandom functions and small-domain pseudorandom permutations used for the hints), the server's view is computationally indistinguishable from a view that does not depend on the queries. This yields client storage $S$ and server time $T$ with $S\cdot T = \tilde O(n)$.

## Proof sketch

The invertible PRF computes the preimage set of an index directly instead of scanning all hints. The relocation graph is maintained as a collection of vertex-disjoint chains and cycles whose distribution depends only on the number of queries (Wang and Ren, Corollary 3.10).

## Depends on

- [Client-preprocessing single-server PIR](client-preprocessing-pir.md)

## Proof depends on

- [The Piano preprocessing PIR scheme](piano-pir.md)

## Sources

- Alexander Hoover, Sarvar Patel, Giuseppe Persiano and Kevin Yeo, "Plinko: Single-Server PIR with Efficient Updates via Invertible PRFs", Advances in Cryptology – EUROCRYPT 2025, Part VI, 2025.
- Zhikun Wang and Ling Ren, "Single-Server Client Preprocessing PIR with Tight Space-Time Trade-off", Advances in Cryptology – EUROCRYPT 2025, 2025.
