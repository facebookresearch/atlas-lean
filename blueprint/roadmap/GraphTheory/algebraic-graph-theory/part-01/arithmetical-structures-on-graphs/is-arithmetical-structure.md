# Arithmetical structure

An arithmetical structure on a graph $G$ with vertex set $V$ is a
pair of labelings $d, r : V \to \mathbb{N}$ such that $d(v) > 0$ and $r(v) > 0$ for every vertex
$v$, $d(v)\, r(v) = \sum_{w \sim v} r(w)$ for every vertex $v$, where the sum runs over the
neighbours $w$ of $v$, and the only natural number dividing every $r(v)$ is $1$. For a finite graph
with adjacency matrix $A$ the middle condition reads $(\operatorname{diag}(d) - A)\, r = 0$.

The neighbour sum is taken to be $0$ when $v$ has infinitely many neighbours, so no arithmetical
structure exists on a graph with a vertex of infinite degree.

## Sources

- Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Definition 2.1 (arXiv numbering).
