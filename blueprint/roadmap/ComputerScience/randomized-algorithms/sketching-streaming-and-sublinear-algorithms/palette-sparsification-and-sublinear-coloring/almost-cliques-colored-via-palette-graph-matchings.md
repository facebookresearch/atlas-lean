# Almost-cliques are list-colorable from random samples via saturating matchings of the palette graph

Let $K$ be a vertex set and suppose every vertex $v \in K$ has a set $A(v)$ of *available* colors (colors in $L(v)$ not used by already colored neighbors of $v$ outside $K$). Let $B_K$ be the bipartite *palette graph* with sides $K$ and $\bigcup_{v} A(v)$ and an edge $\{v, c\}$ whenever $c \in A(v)$.

1. If $B_K$ has a matching saturating $K$, then giving each $v \in K$ its matched color extends the coloring properly to $K$, even if $K$ is a clique.
2. $B_K$ has such a matching if and only if $|\bigcup_{v \in S} A(v)| \ge |S|$ for every $S \subseteq K$ (Hall's condition).
3. (Large matchings in randomly sparsified bipartite graphs.) Let $N \le n$ and $0 \le \delta \le 1/12$, and let $H$ be a bipartite graph with sides $V_1$ and $V_2$ such that $|V_1| \le (1 - 3\delta)N$ and $|V_2| \le 2N$, every vertex of $V_1$ has degree at least $2N/3$ and at most $N$, and the average degree of the vertices of $V_1$ is at least $(1 - \delta)N$. If $H'$ keeps every edge of $H$ independently with probability $p = 90\log n/N$, then with high probability $H'$ has a matching of size $|V_1|$. For an almost-clique $K$ of the $(\Delta + 1)$-coloring proof, with $V_1$ the vertices of $K$ still uncolored, $V_2$ the colors and $H$ the graph of available colors, the palette graph built from the last batch of sampled colors contains such a random subgraph $H'$, so it has a matching saturating $V_1$.

## Proof sketch

Part 1 holds because matched colors are distinct inside $K$ and available with respect to outside neighbors. Part 2 is Hall's theorem, which follows from Kőnig's theorem applied to $B_K$. Part 3 also goes through Hall's condition: a violation is a set $S \subseteq V_1$ whose neighbors in $H'$ all lie in a set $T \subseteq V_2$ with $|T| < |S|$, so $H'$ misses every edge of $H$ between $S$ and $V_2 \setminus T$. The degree bounds force many such edges, and a stochastic-domination comparison of degree sequences together with a union bound over the pairs $(S, T)$, separating small $S$ from large $S$, shows that some violation occurs only with probability $n^{-\Omega(1)}$.

## Depends on

- [Palette sparsification experiment, sampled lists and the conflict graph](palette-sparsification-experiment.md)

## Proof depends on

- [Kőnig's theorem for finite bipartite graphs](../../../../GraphTheory/matchings-and-flows/k-nig-s-theorem/konig-matching-cover.md)

## Sources

- Sepehr Assadi, Yu Chen, Sanjeev Khanna, "Sublinear Algorithms for (Delta + 1) Vertex Coloring", SODA (2019), arXiv:1807.08886.
