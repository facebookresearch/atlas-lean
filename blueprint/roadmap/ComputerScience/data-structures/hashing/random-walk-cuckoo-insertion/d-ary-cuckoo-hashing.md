# d-ary cuckoo hashing and its hashing graph

Let $X \subseteq U$ be a set of $n$ keys, $Y$ a table of $m$ slots, $c = n/m$ the load factor, and $d \ge 2$. Hash functions $h_1, \dots, h_d : U \to Y$ are independent and uniformly random. The *hashing graph* is the bipartite graph on $(X, Y)$ with edges $\{x, h_i(x)\}$ for all $x$ and $i$. A *valid assignment* stores each key $x$ in one of $h_1(x), \dots, h_d(x)$ with no two keys in the same slot, that is, a matching of the hashing graph saturating $X$. A query checks the $d$ slots $h_i(x)$, so queries and deletions take $O(d)$ worst-case time.

## Depends on

- [Cuckoo hash table](../cuckoo-hashing/cuckoo-hashing.md)

## Sources

- Dimitris Fotakis, Rasmus Pagh, Peter Sanders, Paul Spirakis, "Space Efficient Hash Tables with Worst Case Constant Access Time", Theory of Computing Systems 38(2) (2005).
- Rasmus Pagh, Flemming Friche Rodler, "Cuckoo Hashing", Journal of Algorithms 51(2) (2004).
- Tolson Bell, Alan Frieze, "O(1) Insertion for Random Walk d-ary Cuckoo Hashing up to the Load Threshold", FOCS (2024), arXiv:2401.14394.
