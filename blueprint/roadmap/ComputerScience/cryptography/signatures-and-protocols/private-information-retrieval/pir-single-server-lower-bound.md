# Single-server and full-coalition PIR must send the whole database

Let a one-round PIR scheme for $n$-bit databases be perfectly correct. (i) If it has a single server and is perfectly private, then some query $q$ makes the answer map $x \mapsto a(x, q)$ injective, so the communication is at least $n$ bits. (ii) More generally, if the scheme is $t$-private and $|S| \le t$ (all servers may collude), then some joint query makes the joint answer map injective and the total communication is at least $n$ bits; this also holds for indexed schemes with heterogeneous widths, where the bound is $n \le \sum_s \lceil\log_2|A_s|\rceil$. (iii) For blocks of $\ell$ bits, a single server (or a full coalition) must communicate at least $n\ell$ bits, which the trivial download scheme attains; hence nontrivial information-theoretic PIR needs $t < |S|$.

## Proof sketch

Privacy means a query of the coalition occurs for every index with the same probability, so a single joint query $q$ in the support must let reconstruction recover every index $i$ from the answers to $q$; hence the answers to $q$ determine the whole database.

## Depends on

- [Private information retrieval schemes](pir-schemes.md)

## Sources

- Benny Chor, Oded Goldreich, Eyal Kushilevitz and Madhu Sudan, "Private Information Retrieval", Journal of the ACM, 1998.
