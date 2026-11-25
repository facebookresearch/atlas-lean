# Berge's lemma for matching subgraphs

Let $G$ be a simple graph on a finite vertex set and
let $M$ be a matching subgraph of $G$, so that every vertex of $M$ is incident to exactly one
edge of $M$. Then $M$ has the maximum number of edges among all matching subgraphs of $G$ if and
only if there is no $M$-augmenting path: a path in $G$ of positive length between two distinct
vertices $u$ and $v$, neither of which is a vertex of $M$, whose consecutive edges alternate
between edges of $M$ and edges not in $M$.

## Sources

- J. E. Hopcroft and R. M. Karp, "An $n^{5/2}$ algorithm for maximum matchings in bipartite graphs", *SIAM Journal on Computing* 2(4) (1973), 225–231, §2. Corollary 1 (Berge's lemma, derived there from Theorem 1).
- C. Berge, "Two theorems in graph theory", *Proceedings of the National Academy of Sciences of the USA* 43 (1957), 842–844.
