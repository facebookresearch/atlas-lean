# Interaction does not help single-server PIR

Let a single-server PIR protocol for $n$-bit databases, possibly with many rounds of interaction between the user and the server, be perfectly correct and perfectly (information-theoretically) private. Then for every index $i$ at least $2^n$ distinct communications are possible, so at least $n$ bits must be exchanged in the worst case: the trivial protocol that sends the whole database is optimal (Chor, Goldreich, Kushilevitz and Sudan, Section 5.1).

## Proof sketch

Fix $i$. If fewer than $2^n$ communications were possible for $i$, some communication $C$ would have positive probability on two databases $x \ne y$ with index $i$. By privacy, $C$ then has positive probability on $(x, j)$ and on $(y, j)$ for every index $j$, in particular for one with $x_j \ne y_j$; but on communication $C$ the user outputs a single bit, which cannot equal both $x_j$ and $y_j$. Distinguishing $2^n$ communications takes at least $n$ bits.

## Depends on

- [Private information retrieval schemes](pir-schemes.md)
- [Communication cost of a protocol](../../../../TheoryOfComputation/communication-complexity/deterministic-communication-protocols/depth.md)

## Proof depends on

- [Single-server and full-coalition PIR must send the whole database](pir-single-server-lower-bound.md)

## Sources

- Benny Chor, Oded Goldreich, Eyal Kushilevitz and Madhu Sudan, "Private Information Retrieval", Journal of the ACM 45(6), 1998, Section 5.1.
