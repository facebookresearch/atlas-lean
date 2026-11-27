# Multiset equality certifies read-correctness of memory

In offline memory checking where every step $s$ reads an address and writes it back, each write is tagged with the trusted step number $s$, and every read timestamp $t_s$ satisfies $t_s<s$, if $\mathsf{Init}\cup\mathsf{WS}=\mathsf{RS}\cup\mathsf{Final}$ as multisets then every read returned the value most recently written to its address, or its initial value if there was no earlier write. Conversely, an honest memory, which returns the latest entry of each cell with its timestamp, always satisfies the equality and the timestamp checks.

## Proof sketch

Fix an address $a$ and let $s_1<\dots<s_k$ be the steps that access it, in execution order. The triples for $a$ on the left are produced by the initialization, with timestamp $0$, and by the writes at steps $s_1,\dots,s_k$, with timestamps $s_1,\dots,s_k$: these $k+1$ timestamps are distinct, so a triple's timestamp identifies its producer. On the right, the read at step $s_j$ consumes one triple, with timestamp less than $s_j$, and $\mathsf{Final}$ consumes one more, so the multiset equality is a bijection between producers and consumers that matches equal triples. Induct in execution order: if the reads at $s_1,\dots,s_{j-1}$ consumed the triples of the initialization and of the writes at $s_1,\dots,s_{j-2}$, then the read at $s_j$ must consume a producer with timestamp below $s_j$ that is still unconsumed, and the only one is the write at $s_{j-1}$ (the initialization for $j=1$). Hence each read returns the value of the latest earlier write, and $\mathsf{Final}$ consumes the write at $s_k$.

## Depends on

- [Offline memory checking with timestamps](offline-memory-checking.md)

## Sources

- Manuel Blum, Will Evans, Peter Gemmell, Sampath Kannan, Moni Naor, "Checking the Correctness of Memories", Algorithmica (1994).
- Arasu Arun, Srinath Setty, Justin Thaler, "Jolt: SNARKs for Virtual Machines via Lookups", EUROCRYPT (2024), IACR ePrint 2023/1217, Section 3.2 and Appendix B.
