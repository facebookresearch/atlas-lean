# Multiset equality certifies read-correctness of memory

In offline memory checking with strictly increasing write timestamps (each write's timestamp exceeds the timestamp of the read it follows), if $\mathsf{Init}\cup\mathsf{WS}=\mathsf{RS}\cup\mathsf{Final}$ as multisets then every read returned the value most recently written to (or initialized at) its address. Conversely, an honest memory always satisfies the equality.

## Proof sketch

For a fixed address, order its triples by timestamp. Each read consumes one triple from the left side and each write produces one with a larger timestamp; the multiset equality forces a perfect matching between produced and consumed triples. Strictly increasing timestamps rule out a read consuming a triple not yet produced or a stale one, by induction on time; the final set absorbs the last triple of each address.

## Depends on

- [Offline memory checking with timestamps](offline-memory-checking.md)

## Proof depends on

- [Offline memory checking with timestamps](offline-memory-checking.md)

## Sources

- Manuel Blum, Will Evans, Peter Gemmell, Sampath Kannan, Moni Naor, "Checking the Correctness of Memories", Algorithmica (1994).
