# Almost-cliques are list-colorable from random samples via saturating matchings of the palette graph

Let $K$ be a vertex set and suppose every vertex $v \in K$ has a set $A(v)$ of *available* colors (colors in $L(v)$ not used by already colored neighbors of $v$ outside $K$). Let $B_K$ be the bipartite *palette graph* with sides $K$ and $\bigcup_{v} A(v)$ and an edge $\{v, c\}$ whenever $c \in A(v)$.

1. If $B_K$ has a matching saturating $K$, then giving each $v \in K$ its matched color extends the coloring properly to $K$, even if $K$ is a clique.
2. $B_K$ has such a matching if and only if $|\bigcup_{v \in S} A(v)| \ge |S|$ for every $S \subseteq K$ (Hall's condition).
3. If the sets $A(v)$, $v \in K$, are independent uniformly random subsets of size $s$ of a common set $P$ with $|P| \ge |K|$, then for every $c > 0$ there is $C = C(c)$ such that $s \ge C\log n$ and $|K| \le n$ imply that $B_K$ has a matching saturating $K$ with probability at least $1 - n^{-c}$.

## Proof sketch

Part 1 holds because matched colors are distinct inside $K$ and available with respect to outside neighbors. Part 2 is Hall's theorem, which follows from Kőnig's theorem applied to $B_K$. For part 3, Hall's condition fails only if some $S \subseteq K$ with $|S| = j$ has all its lists inside a set $T \subseteq P$ with $|T| = j - 1$; the union bound over $S$ and $T$ gives at most $\binom{|K|}{j}\binom{|P|}{j-1}\big((j-1)/|P|\big)^{s j}$, which is at most $n^{-c-1}$ for every $j$ once $s \ge C \log n$, by separating $j \le |P|/2$ from $j > |P|/2$ and writing the second case in terms of $|P| - j$.

## Depends on

- [Palette sparsification experiment, sampled lists and the conflict graph](palette-sparsification-experiment.md)

## Proof depends on

- [Kőnig's theorem for finite bipartite graphs](../../../../GraphTheory/matchings-and-flows/k-nig-s-theorem/konig-matching-cover.md)

## Sources

- Sepehr Assadi, Yu Chen, Sanjeev Khanna, "Sublinear Algorithms for (Delta + 1) Vertex Coloring", SODA (2019), arXiv:1807.08886.
