# Harutyunyan's three-fifths conjecture is false

There exist a finite type $V$ and an oriented digraph $D$ on $V$ whose underlying simple graph is planar such that every acyclic set $S \subseteq V$ of $D$ satisfies $5\,|S| < 3\,|V|$, that is, has fewer than three fifths of the vertices.

For a finite type $V$ and a digraph $D$ on $V$ (an arc relation $u \to v$, so there are no parallel arcs), call $D$ oriented if it has no loops and no pair of opposite arcs, and call a set $S \subseteq V$ acyclic if no directed closed walk of positive length uses only arcs between vertices of $S$. The underlying simple graph of $D$ joins distinct $u, v$ whenever $u \to v$ or $v \to u$; it is planar if $V$ is empty or there is an injective map $f \colon V \to \mathbb{R}^2$ such that, for any two different edges $vw$ and $xy$, the closed segments $[f(v), f(w)]$ and $[f(x), f(y)]$ meet only in points of $\{f(v), f(w)\} \cap \{f(x), f(y)\}$.

Knauer, Valicov and Wenger construct planar oriented graphs on $n$ vertices whose largest acyclic sets have at most $\lceil (n+1)/2 \rceil$ vertices. That is, the proposition [Harutyunyan's three-fifths conjecture for planar oriented graphs](conjecture.md) is false.

## Sources

- Kolja Knauer, Petru Valicov and Paul S. Wenger, *Planar digraphs without large acyclic sets*, arXiv:1504.06726v2 (2016), https://arxiv.org/abs/1504.06726v2.
