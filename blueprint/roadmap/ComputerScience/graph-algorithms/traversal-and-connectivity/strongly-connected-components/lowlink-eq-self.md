# $\mathrm{LOWLINK}(v) = v$

Tarjan defines $\mathrm{LOWLINK}(v)$ as the smallest-numbered vertex that is in the same strongly
connected component as $v$ and is reachable from $v$ by traversing zero or more tree arcs
followed by at most one frond or cross-link. The condition $\mathrm{LOWLINK}(v) = v$ says that
this minimum is $v$: for
every descendant $d$ of $v$ and every edge $(d, w)$ with $w$ strongly connected to $v$,
$\mathrm{num}(v) \le \mathrm{num}(w)$. Allowing any final edge, not only fronds and cross-links,
does not change the minimum: tree arcs and edges from ancestors to descendants lead to
descendants of $v$, which are numbered after $v$.

Tarjan's displayed formula asks instead that the tail $u$ of the final edge and its head $w$ lie in
the same strongly connected component; his prose, followed here, asks that $w$ lie in the
component of $v$. The minimum is the same: if $u$ and $w$ lie in a component $C' \ne C(v)$, the
root of $C'$ is a descendant of $v$ (Corollary 11), so $w$ is numbered after $v$; and if
$w \in C(v)$, then $u$, which lies on the tree path from $v$ and reaches $w$, is in $C(v)$ as well.

## Sources

- R. E. Tarjan, *Depth-first search and linear graph algorithms*, SIAM J. Comput. 1(2) (1972)
  146–160, §4 (definition of LOWLINK).
