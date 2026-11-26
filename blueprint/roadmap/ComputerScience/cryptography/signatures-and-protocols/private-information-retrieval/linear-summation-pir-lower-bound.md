# Lower bound for two-server linear-summation PIR

A two-server PIR scheme is of *linear-summation type* if each query is a set $q \subseteq [n]$, each server answers with the parity $\bigoplus_{j \in q} x_j$, and the user reconstructs $x_i$ as the XOR of the two answers. In every perfectly correct and private linear-summation scheme, if server $s$ can receive the set $v$, then it can also receive $v \oplus \{j\}$ for every $j$ (the two servers' sets always differ by exactly $\{i\}$ and privacy makes the supports index independent); consequently each server can receive at least $2^{n-1}$ sets and its queries have length at least $n - 1$ bits.

## Proof sketch

Correctness forces the two queries for index $i$ to differ by $\{i\}$; privacy makes each server's query support the same set $V$ for all indices, so $V$ is closed under symmetric difference with every singleton and contains at least half of all subsets.

## Depends on

- [Private information retrieval schemes](pir-schemes.md)

## Sources

- Benny Chor, Oded Goldreich, Eyal Kushilevitz and Madhu Sudan, "Private Information Retrieval", Journal of the ACM, 1998.
