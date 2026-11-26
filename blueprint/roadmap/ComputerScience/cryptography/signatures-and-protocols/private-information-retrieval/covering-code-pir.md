# Covering-code PIR schemes

Let $c_1, \dots, c_k \in \{0,1\}^d$ be distinct codewords of a covering code of radius $1$, i.e. every $\sigma \in \{0,1\}^d$ is at Hamming distance at most $1$ from some $c_j$. Then there is a perfectly correct and private $k$-server PIR scheme in which server $j$ receives the subcube query of $c_j$ and also answers, for each neighbour $\sigma$ it covers, all $\ell = n^{1/d}$ possible queries of $\sigma$ (which differ from its own query in one coordinate set by a single element); if each word outside the code is assigned to one server whose codeword is at distance $1$ from it, and $M_j$ is the set of words assigned to server $j$, the communication is exactly $k\,d\,\ell + \sum_j (1 + |M_j|\,\ell)$ bits, which is $O(k\, d\, n^{1/d})$. The balancedness requirement $k(d + 1) = 2^d$ is not needed. Volume bound: since a server and its $|M_j|$ emulated neighbours cover at most $|M_j| + 1$ words, $2^d \le \sum_j (|M_j| + 1)$. In particular, with $d = 3$ and the covering code $\{000, 111\}$, two servers retrieve a bit with $O(n^{1/3})$ communication; more generally radius-$r$ covers give schemes in which each server emulates all words within distance $r$.

## Proof sketch

A server holding the query of $c_j$ can compute the parity of every subcube whose query differs from its own in coordinate $m$ by adding or removing a single element of $[\ell]$ from the $m$-th set, so it emulates the answers of the neighbour $c_j \oplus e_m$ by sending $\ell$ bits. The XOR of the subcube answers of all $2^d$ virtual servers is $x_i$, and the queries the real servers see are those of the subcube scheme, hence private.

## Depends on

- [Private information retrieval schemes](pir-schemes.md)

## Proof depends on

- [The two-server and subcube XOR PIR schemes](subcube-pir-schemes.md)

## Sources

- Benny Chor, Oded Goldreich, Eyal Kushilevitz and Madhu Sudan, "Private Information Retrieval", Journal of the ACM, 1998.
