# A partial class of VC dimension one with no finite-VC disambiguation

For every $n$ there is a partial concept class $H_n \subseteq \{0,1,\star\}^{[n]}$ with $\mathrm{VC}(H_n) = 1$ and teaching dimension at most $2$ such that every disambiguation $\bar H$ of $H_n$ has size at least $n^{(\log n)^{1 - o(1)}}$; consequently $\mathrm{LD}(\bar H) \ge \mathrm{VC}(\bar H) \ge (\log n)^{1 - o(1)}$. Taking a disjoint union over $n$ gives a partial class $H_\infty$ on a countable domain with $\mathrm{VC}(H_\infty) = 1$ every disambiguation of which has infinite VC dimension. In particular, there are learnable partial classes that are not captured by any learnable total class.

## Proof sketch

Encode a graph $G$ on $n$ vertices by the partial class whose concepts are the cliques (labelled $1$) against the independent sets (labelled $0$) of $G$, with $\star$ elsewhere; since a clique and an independent set share at most one vertex, the VC dimension is one. A disambiguation of small size corresponds to a small nondeterministic communication protocol separating cliques from independent sets of $G$, so the Göös graphs and the resolution of the Alon–Saks–Seymour problem by Balodis, Ben-David, Göös, Jain and Kothari, which give superpolynomial lower bounds for clique versus independent set, force every disambiguation to have size $n^{(\log n)^{1-o(1)}}$. By the Sauer–Shelah–Perles lemma, size $N$ on $n$ points forces VC dimension at least $\log N / \log n$.

## Depends on

- [Partial concept classes and their VC and Littlestone dimensions](partial-concept-class.md)
- [Disambiguations of partial concept classes](disambiguation.md)

## Proof depends on

- [Sauer bound for the growth function](../../../../../not-yet-classified/growth-function/growth-function-le-sum.md)

## Sources

- N. Alon, S. Hanneke, R. Holzman, S. Moran, "A Theory of PAC Learnability of Partial Concept Classes", FOCS (2021), arXiv:2107.08444.
