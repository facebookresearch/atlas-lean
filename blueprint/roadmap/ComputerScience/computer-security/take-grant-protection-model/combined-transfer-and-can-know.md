# The can·know predicate, rwtg-paths and connections

Let $G_0$ be a [protection graph](take-grant-protection-graphs.md). The predicate $\mathrm{can{\cdot}know}(x, y, G_0)$ holds if and only if there is a sequence of
protection graphs $G_0, \dots, G_n$, each obtained from the previous one by a de jure rule or a [de facto rule](de-facto-rules.md), such that $G_n$ has an edge from
$x$ to $y$ labelled $r$ or an edge from $y$ to $x$ labelled $w$, and if that edge is explicit then its source is a subject.

An *rwtg-path* is a nonempty sequence $v_0, \dots, v_n$ of distinct vertices such that consecutive vertices are joined by an edge, in either direction, whose label
contains $t$, $g$, $r$ or $w$; its associated words over $\{\vec t, \overleftarrow t, \vec g, \overleftarrow g, \vec r, \overleftarrow r, \vec w, \overleftarrow w\}$ are formed as for
[tg-paths](tg-paths-islands-spans-and-bridges.md). A vertex $v_0$

- *rw-initially spans to* $v_n$ if $v_0$ is a subject and some rwtg-path between them has an associated word in $\vec t^{\,*} \vec w \cup \{\nu\}$;
- *rw-terminally spans to* $v_n$ if $v_0$ is a subject and some rwtg-path between them has an associated word in $\vec t^{\,*} \vec r$.

A *connection* is an rwtg-path whose endpoints are both subjects and which has an associated word in
$C = \vec t^{\,*} \vec r \cup \overleftarrow w\, \overleftarrow t^{\,*} \cup \vec t^{\,*} \vec r\, \overleftarrow w\, \overleftarrow t^{\,*}$.

## Depends on

- [Take–grant protection graphs](take-grant-protection-graphs.md)
- [De facto rules](de-facto-rules.md)
- [tg-paths, islands, spans and bridges](tg-paths-islands-spans-and-bridges.md)

## Sources

- M. Bishop, "Conspiracy and information flow in the take-grant protection model", *Journal of Computer Security* 4(4):331–359, 1996, author copy at <http://nob.cs.ucdavis.edu/bishop/papers/1996-jcs/tgconsp.pdf>: Section 2, the definitions of can·know, rwtg-path, rw-initially spans, rw-terminally spans and connection.
