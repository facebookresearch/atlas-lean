# A partial class of VC dimension one with no finite-VC disambiguation

For every $n$ there is a partial concept class $H_n \subseteq \{0,1,\star\}^{[n]}$ with $\mathrm{VC}(H_n) = 1$ and teaching dimension at most $2$ such that every disambiguation $\bar H$ of $H_n$ has size at least $n^{(\log n)^{1 - o(1)}}$; consequently $\mathrm{LD}(\bar H) \ge \mathrm{VC}(\bar H) \ge (\log n)^{1 - o(1)}$. Taking a disjoint union over $n$ gives a partial class $H_\infty$ on a countable domain with $\mathrm{VC}(H_\infty) = 1$ every disambiguation of which has infinite VC dimension. In particular, there are learnable partial classes that are not captured by any learnable total class.

## Proof sketch

The class is extracted from graphs that witness the superpolynomial separation for the clique versus independent set problem in communication complexity, obtained by Göös and by Ben-David, Hatami and Tal, and sharpened by Balodis, Ben-David, Göös, Jain and Kothari (which also resolves the Alon–Saks–Seymour problem): the structure of a clique meeting an independent set in at most one vertex keeps the VC dimension at one, while a small disambiguation would give a small covering that the separation rules out. By the Sauer–Shelah–Perles lemma, a total class of size $N$ on $n$ points has VC dimension at least of order $\log N / \log n$, which gives the VC bound; a disjoint union over $n$ gives $H_\infty$.

## Depends on

- [Partial concept classes and their VC and Littlestone dimensions](partial-concept-class.md)
- [Disambiguations of partial concept classes](disambiguation.md)

## Proof depends on

- [Sauer bound for the growth function](../../../../../not-yet-classified/growth-function/growth-function-le-sum.md)

## Sources

- N. Alon, S. Hanneke, R. Holzman, S. Moran, "A Theory of PAC Learnability of Partial Concept Classes", FOCS (2021), arXiv:2107.08444, Theorem 11 and its discussion in Section 2.4.3.
