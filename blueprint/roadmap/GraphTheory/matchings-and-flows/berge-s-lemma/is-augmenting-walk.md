# Augmenting path

Let $M$ be a finite set of edges of a simple graph $G$, in practice a matching. A walk $p$ from $u$ to $v$ in $G$ is *$M$-augmenting* if $u \ne v$, $p$ has positive length and no repeated vertex, neither $u$ nor $v$ lies on an edge of $M$, and consecutive edges of $p$ alternate between edges in $M$ and edges not in $M$. Since the endpoints are not covered by $M$, the first and last edges are not in $M$, so $p$ has odd length and one more edge outside $M$ than in $M$.

This is the predicate in the statement of [Berge's lemma](berge.md), named so that later statements can refer to it.

## Sources

- J. E. Hopcroft and R. M. Karp, "An $n^{5/2}$ algorithm for maximum matchings in bipartite graphs", *SIAM Journal on Computing* 2(4) (1973), 225–231, §2. (definition of an augmenting path).
