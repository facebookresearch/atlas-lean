# tg-paths, islands, spans and bridges

Let $G$ be a [protection graph](take-grant-protection-graphs.md). A *tg-path* is a nonempty sequence of vertices $v_0, \dots, v_k$ such that for every $i < k$ the
vertices $v_i$ and $v_{i+1}$ are joined by an edge, in either direction, whose label contains $t$ or $g$. Vertices are *tg-connected* if a tg-path joins them,
and an *island* is a maximal tg-connected subgraph all of whose vertices are subjects.

A tg-path has associated words over the alphabet $\{\vec t, \overleftarrow t, \vec g, \overleftarrow g\}$: the $i$-th letter is $\vec t$ (respectively $\vec g$) for an
edge from $v_{i-1}$ to $v_i$ containing $t$ (respectively $g$), and $\overleftarrow t$ (respectively $\overleftarrow g$) for an edge from $v_i$ to $v_{i-1}$; a path with
$k = 0$ has the empty word $\varepsilon$. A tg-path whose first vertex $v_0$ is a subject is

- an *initial span* (from $v_0$ to $v_k$) if it has an associated word in $\vec t^{\,*} \vec g \cup \{\varepsilon\}$;
- a *terminal span* (from $v_0$ to $v_k$) if it has an associated word in $\vec t^{\,*}$;
- a *bridge* if $v_k$ is also a subject and it has an associated word in $\vec t^{\,*} \cup \overleftarrow t^{\,*} \cup \vec t^{\,*} \vec g\, \overleftarrow t^{\,*} \cup \vec t^{\,*} \overleftarrow g\, \overleftarrow t^{\,*}$.

We say that $v_0$ *initially* (respectively *terminally*) *spans to* $v_k$.

## Depends on

- [Take–grant protection graphs](take-grant-protection-graphs.md)

## Sources

- M. Bishop and L. Snyder, *The Transfer of Information and Authority in a Protection System*, Research Report 166, Department of Computer Science, Yale University, July 1979, <http://nob.cs.ucdavis.edu/~bishop/notes/1979-yalecs-166/yale-166.pdf>: Section 4, the definitions of tg-paths, islands, initial and terminal spans and bridges (pp. 17–19).
