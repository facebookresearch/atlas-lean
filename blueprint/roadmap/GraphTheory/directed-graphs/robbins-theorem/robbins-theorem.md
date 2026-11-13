# Robbins' theorem, allowing the empty graph

Let $G$ be a simple graph on a finite,
possibly empty, vertex set $V$. Then every vertex of $G$ is reachable from every vertex and,
after deleting any single edge of $G$, every vertex is still reachable from every vertex, if
and only if $G$ has a strongly connected orientation: a relation $D$ on $V$ such that $D(u, v)$
holds only when $u$ and $v$ are adjacent, for every edge $uv$ exactly one of $D(u, v)$ and
$D(v, u)$ holds, and every vertex $v$ can be reached from every vertex $u$ by a finite,
possibly empty, sequence of $D$-steps.

For nonempty $V$ the left-hand condition says that $G$ is 2-edge-connected; for empty $V$ both
sides hold.

## Sources

- https://en.wikipedia.org/wiki/Robbins%27_theorem
