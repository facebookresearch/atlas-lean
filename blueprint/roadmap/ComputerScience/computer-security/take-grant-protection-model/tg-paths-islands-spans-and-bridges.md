# tg-paths, islands, spans and bridges

Let $G$ be a [protection graph](take-grant-protection-graphs.md). A *tg-path* is a nonempty sequence $v_0, \dots, v_n$ of **distinct** vertices such that for every
$i < n$ the vertices $v_i$ and $v_{i+1}$ are joined by an edge, in either direction, whose label contains $t$ or $g$. Vertices are *tg-connected* if a tg-path joins
them, and an *island* is a maximal tg-connected subgraph all of whose vertices are subjects.

A tg-path has associated words over $\{\vec t, \overleftarrow t, \vec g, \overleftarrow g\}$: the $i$-th letter is $\vec t$ (respectively $\vec g$) for an edge from $v_{i-1}$ to
$v_i$ whose label contains $t$ (respectively $g$), and $\overleftarrow t$ (respectively $\overleftarrow g$) for such an edge from $v_i$ to $v_{i-1}$; a path of length $0$ has the
empty word $\nu$. Then:

- $v_0$ *initially spans to* $v_n$ if $v_0$ is a subject and some tg-path between them has an associated word in $\vec t^{\,*} \vec g \cup \{\nu\}$;
- $v_0$ *terminally spans to* $v_n$ if $v_0$ is a subject and some tg-path between them has an associated word in $\vec t^{\,*}$;
- a *bridge* is a tg-path whose endpoints $v_0$ and $v_n$ are both subjects and which has an associated word in
  $B = \vec t^{\,*} \cup \overleftarrow t^{\,*} \cup \vec t^{\,*} \vec g\, \overleftarrow t^{\,*} \cup \vec t^{\,*} \overleftarrow g\, \overleftarrow t^{\,*}$.

## Depends on

- [Take–grant protection graphs](take-grant-protection-graphs.md)

## Sources

- M. Bishop, "Conspiracy and information flow in the take-grant protection model", *Journal of Computer Security* 4(4):331–359, 1996, author copy at <http://nob.cs.ucdavis.edu/bishop/papers/1996-jcs/tgconsp.pdf>: Section 2, the definitions of tg-path, tg-connected, island, the associated words, initially spans, terminally spans and bridge.
