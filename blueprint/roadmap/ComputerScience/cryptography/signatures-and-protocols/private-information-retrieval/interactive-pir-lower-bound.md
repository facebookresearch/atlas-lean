# Interaction does not help single-server PIR

Let a single-server PIR protocol of arbitrary many rounds (a protocol tree with independent user and server coins) be perfectly correct and perfectly private for $n$-bit databases over an alphabet $\beta$. Then for fixed coins the transcript determines the database, every index has at least $|\beta|^n$ possible transcripts, and the protocol tree has depth at least $n \log_2|\beta|$, i.e. at least $n$ bits are exchanged in the worst case (and $n\ell$ bits for $\ell$-bit blocks). The same bound holds for adaptive multi-round $k$-server protocols with isolated channels when all servers may collude ($|S| \le t$).

## Proof sketch

If two databases reached the same leaf with the same coins, the rectangle property of communication protocols would give the same transcript on a mixed input, and privacy together with correctness would then force equal entries at every index. Counting leaves gives the depth bound.

## Depends on

- [Private information retrieval schemes](pir-schemes.md)
- [Communication cost of a protocol](../../../../TheoryOfComputation/communication-complexity/deterministic-communication-protocols/depth.md)

## Proof depends on

- [Single-server and full-coalition PIR must send the whole database](pir-single-server-lower-bound.md)

## Sources

- Benny Chor, Oded Goldreich, Eyal Kushilevitz and Madhu Sudan, "Private Information Retrieval", Journal of the ACM, 1998.
