# Embedding an expander with low vertex congestion certifies directed vertex expansion

Let $G=(V,E)$ be a directed graph. A *vertex cut* is a partition $(L,S,R)$ of $V$ with $L,R\ne\emptyset$ such that $E(L,R)=\emptyset$ or $E(R,L)=\emptyset$; it is *$\phi$-vertex-sparse* if $|S|<\phi\min\{|L|,|R|\}$, and $G$ is a *$\phi$-vertex expander* if it has no $\phi$-vertex-sparse vertex cut. An *embedding* of a weighted graph $W=(V,E',c)$ into $G$ assigns to each edge $(a,b)\in E'$ a collection of directed $a$-$b$ paths in $G$ with values summing to $c(a,b)$; it has *vertex congestion* $\mathrm{cong}$ if every vertex of $G$ lies on paths of total value at most $\mathrm{cong}$.

If $W$ is a $\phi$-expander (with weighted volumes) in which every vertex has weighted in- and out-degree at least $1$, and $W$ embeds into $G$ with vertex congestion $\mathrm{cong}$, then $G$ is a $(\phi/\mathrm{cong})$-vertex expander.

## Proof sketch

Take a vertex cut $(L,S,R)$ with $|L|\le|R|$ and, say, $E(L,R)=\emptyset$ (the other cases are symmetric, using in-edges of $W$). The edges of $W$ leaving $L$ have total weight at least $\phi\,\mathrm{vol}_W(L)\ge\phi|L|$ because every vertex of $W$ has weighted degree at least $1$. Each embedded path of such an edge leaves $L$ in $G$ and cannot jump directly to $R$, so it passes through $S$; hence their total value is at most $|S|\cdot\mathrm{cong}$, which gives $|S|\ge\phi|L|/\mathrm{cong}$.

## Depends on

- [Directed phi-expanders, phi-sparse directed cuts, and phi-expanding terminal edge sets](directed-phi-expanders.md)
- [Directed paths](../connectivity-of-directed-graphs/is-directed-path.md)
- [Internally disjoint directed paths](../connectivity-of-directed-graphs/has-internally-disjoint-paths.md)

## Proof depends on

- [Directed phi-expanders, phi-sparse directed cuts, and phi-expanding terminal edge sets](directed-phi-expanders.md)
- [Directed paths](../connectivity-of-directed-graphs/is-directed-path.md)

## Sources

- Aaron Bernstein, Maximilian Probst Gutenberg, Thatchaphol Saranurak, "Deterministic Decremental Reachability, SCC, and Shortest Paths via Directed Expanders and Congestion Balancing", FOCS (2020), arXiv:2009.02584.
