# Q-hierarchical conjunctive queries can be maintained under updates

A dynamic algorithm for a conjunctive query receives the query and an initial database, preprocesses them, and then
processes single-tuple insertions and deletions; the preprocessing, update, delay, answer and counting times are measured on
a random access machine as in [enumeration with constant delay](enumeration-with-linear-preprocessing-and-constant-delay.md),
with $n$ the size of the active domain. Here conjunctive queries are those of the source: every argument of every atom is a variable, and the output lists the
free variables, each once; queries with constants in atoms are not covered.

**Theorem.** There is a dynamic algorithm that receives a [q-hierarchical](q-hierarchical-conjunctive-queries.md) conjunctive
query $\varphi$ and a database $D_0$, builds a data structure in time $\mathrm{poly}(\varphi) \cdot O(\|D_0\|)$, handles each update
in time $\mathrm{poly}(\varphi)$, and allows one to enumerate $\varphi(D)$ with delay $\mathrm{poly}(\varphi)$ and to compute
$|\varphi(D)|$ in time $O(1)$, where $D$ is the current database. In particular, for each fixed query, q-hierarchical Boolean queries are answered and counts are
output in constant time after each update.

## Depends on

- [Enumeration with linear preprocessing and constant delay](enumeration-with-linear-preprocessing-and-constant-delay.md)
- [Q-hierarchical conjunctive queries](q-hierarchical-conjunctive-queries.md)

## Sources

- C. Berkholz, J. Keppeler and N. Schweikardt, "Answering conjunctive queries under updates", *Proceedings of the 36th ACM PODS*, 2017, pp. 303–318; arXiv:1702.06370 <https://arxiv.org/abs/1702.06370>, Theorem 3.2, proved in Section 6.
