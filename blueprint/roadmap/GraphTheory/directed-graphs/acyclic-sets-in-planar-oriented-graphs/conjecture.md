# Harutyunyan's three-fifths conjecture for planar oriented graphs

The statement that every finite planar oriented graph has an acyclic set containing at least three fifths of its vertices: for every finite type $V$ and every oriented digraph $D$ on $V$ whose underlying simple graph is planar, there is a finite set $S \subseteq V$ that is acyclic in $D$ and satisfies $3\,|V| \le 5\,|S|$.

For a finite type $V$ and a digraph $D$ on $V$ (an arc relation $u \to v$, so there are no parallel arcs), call $D$ oriented if it has no loops and no pair of opposite arcs, and call a set $S \subseteq V$ acyclic if no directed closed walk of positive length uses only arcs between vertices of $S$. The underlying simple graph of $D$ joins distinct $u, v$ whenever $u \to v$ or $v \to u$; it is planar if $V$ is empty or there is an injective map $f \colon V \to \mathbb{R}^2$ such that, for any two different edges $vw$ and $xy$, the closed segments $[f(v), f(w)]$ and $[f(x), f(y)]$ meet only in points of $\{f(v), f(w)\} \cap \{f(x), f(y)\}$.

The inequality $3|V| \le 5|S|$ is $|S| \ge \frac{3}{5}|V|$ with no rounding. Stated here as a proposition; its resolution: [Harutyunyan's three-fifths conjecture is false](conjecture-refuted.md).
