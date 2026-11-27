# The two-server and subcube XOR PIR schemes

(i) *Two-server scheme:* the user draws a uniform subset $T \subseteq [n]$ and sends $T$ to server $1$ and $T \oplus \{i\}$ to server $2$; each server returns the parity of the database on its set, and the XOR of the answers is $x_i$. Each query is a uniform subset, so the scheme is perfectly correct and private, with $n + 1$ bits per server. (ii) *Subcube scheme:* arrange the database as a $d$-dimensional cube $[\ell]^d$ with $\ell = \lceil n^{1/d}\rceil$; for $2^d$ servers indexed by $\sigma \in \{0,1\}^d$, the user draws uniform subsets $T_1^0, \dots, T_d^0 \subseteq [\ell]$, sets $T_j^1 = T_j^0 \oplus \{i_j\}$, and sends $(T_1^{\sigma_1}, \dots, T_d^{\sigma_d})$ to server $\sigma$, which returns the parity of $x$ on the subcube $T_1^{\sigma_1}\times\dots\times T_d^{\sigma_d}$. The XOR of all answers is $x_i$, every server sees uniform subsets, and the communication is $2^d(d\,\lceil n^{1/d}\rceil + 1)$ bits.

## Proof sketch

In the XOR of all $2^d$ subcube parities, every cell other than $i$ is counted an even number of times.

## Depends on

- [Private information retrieval schemes](pir-schemes.md)

## Sources

- Benny Chor, Oded Goldreich, Eyal Kushilevitz and Madhu Sudan, "Private Information Retrieval", Journal of the ACM, 1998.
