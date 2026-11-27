# Lower bound for two-server linear-summation PIR

A two-server PIR scheme is of *linear-summation type* if each query is a set $q \subseteq [n]$, each server answers with the parity $\bigoplus_{j \in q} x_j$, and the user reconstructs $x_i$ as the XOR of the two answers. In every perfectly correct and private linear-summation scheme, if server $1$ can receive the set $v$, then server $2$ can receive $v \oplus \{j\}$ for every $j$, and hence server $1$ can receive $v \oplus \{j\} \oplus \{j'\}$ for all $j, j'$ (the two servers' sets always differ by exactly $\{i\}$ and privacy makes the supports index independent); consequently each server can receive every set of the parity class of any set it can receive, hence at least $2^{n-1}$ sets and its queries have length at least $n - 1$ bits.

## Proof sketch

Correctness forces the two queries for index $i$ to differ by $\{i\}$; privacy makes each server's query support $V_s$ the same for all indices, so $v \in V_1$ implies $v \oplus \{j\} \in V_2$ for every $j$ and hence $v \oplus \{j\} \oplus \{j'\} \in V_1$; thus $V_1$ contains the whole parity class of $v$, which is half of all subsets, and symmetrically for $V_2$.

## Depends on

- [Private information retrieval schemes](pir-schemes.md)

## Sources

- Benny Chor, Oded Goldreich, Eyal Kushilevitz and Madhu Sudan, "Private Information Retrieval", Journal of the ACM, 1998.
