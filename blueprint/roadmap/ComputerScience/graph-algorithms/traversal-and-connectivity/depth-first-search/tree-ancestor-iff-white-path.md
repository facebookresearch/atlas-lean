# White-path theorem

Under the [numbering properties of depth-first search](../strongly-connected-components/is-dfsnumbering.md),
$u$ is an ancestor of $v$ in the depth-first forest if and only if there is a path of edges from
$u$ to $v$ all of whose vertices have number at least that of $u$, that is, are still new
(unvisited) when the search reaches $u$.

A tree path is such a path. Conversely, along such a path the first vertex $x$ that is not a
descendant of $u$ would be entered by an edge $(w, x)$ from a descendant $w$ of $u$; that edge
leads to a descendant of $w$ or to a vertex numbered before $w$, and in the second case $x$ is
numbered between $u$ and $w$, hence is a descendant of $u$ because descendants are numbered
consecutively.

## Sources

- J. Erickson, *Algorithms* (1st ed., 2019), Chapter 6, Lemma 6.1, (a) ⇔ (d).
