# Private block retrieval

For databases of $n$ blocks of $\ell$ bits: (i) any $k$-server bit-PIR scheme with communication $C(n)$ yields block retrieval by running it on each of the $\ell$ bit-slices with shared queries, so the queries are sent once and only the answers are multiplied by $\ell$; (ii) splitting the database into $\ell$ chunks and retrieving one block from each chunk position, with dummy zero bits in the other chunks, gives schemes in which the servers' answers in chunk $j$ sum to the requested bit and to $0$ elsewhere; these transformations preserve perfect correctness and $t$-privacy. In particular, the single-server (or full-coalition) block retrieval needs exactly $n\ell$ bits, attained by downloading.

## Proof sketch

Correctness and privacy of the transformations reduce to those of the bit scheme, since every server's query distribution is unchanged.

## Depends on

- [Private information retrieval schemes](pir-schemes.md)

## Proof depends on

- [Single-server and full-coalition PIR must send the whole database](pir-single-server-lower-bound.md)

## Sources

- Benny Chor, Oded Goldreich, Eyal Kushilevitz and Madhu Sudan, "Private Information Retrieval", Journal of the ACM, 1998.
