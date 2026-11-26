# Combined transfer and the can·know predicate

Let $G_0$ be a [protection graph](take-grant-protection-graphs.md). A *combined transfer* applies any sequence of de jure rules (Take, Grant, Create, Remove), which
match explicit edges only, and [de facto rules](de-facto-rules-and-admissible-rw-paths.md) (Post, Pass, Spy, Find), which match explicit or implicit edges. For
distinct vertices $p, q$, $\mathrm{can{\cdot}know}(p, q, G_0)$ holds if there are graphs $G_1, \dots, G_n$ with $G_0 \vdash^* G_n$ by combined transfers such that $G_n$
has an edge, explicit or implicit, from $p$ to $q$ labelled $r$.

An *rwtg-path* joins consecutive vertices by edges whose labels contain $r$, $w$, $t$ or $g$, and has associated words over
$\{\vec t, \overleftarrow t, \vec g, \overleftarrow g, \vec r, \overleftarrow r, \vec w, \overleftarrow w\}$ as for [tg-paths](tg-paths-islands-spans-and-bridges.md). An
rwtg-path $v_0, \dots, v_k$ ($k > 0$) whose first vertex $v_0$ is a subject is an *rw-initial span* if it has an associated word in $\vec t^{\,*} \vec w$ and an
*rw-terminal span* if it has an associated word in $\vec t^{\,*} \vec r$. The languages of *bridges* and *connections* are
$$B = \vec t^{\,*} \cup \overleftarrow t^{\,*} \cup \vec t^{\,*} \vec g\, \overleftarrow t^{\,*} \cup \vec t^{\,*} \overleftarrow g\, \overleftarrow t^{\,*}, \qquad
C = \vec t^{\,*} \vec r \cup \overleftarrow w\, \overleftarrow t^{\,*} \cup \vec t^{\,*} \vec r\, \overleftarrow w\, \overleftarrow t^{\,*}.$$

## Depends on

- [Take–grant protection graphs](take-grant-protection-graphs.md)
- [De facto rules and admissible rw-paths](de-facto-rules-and-admissible-rw-paths.md)
- [tg-paths, islands, spans and bridges](tg-paths-islands-spans-and-bridges.md)

## Sources

- M. Bishop and L. Snyder, *The Transfer of Information and Authority in a Protection System*, Research Report 166, Department of Computer Science, Yale University, July 1979, <http://nob.cs.ucdavis.edu/~bishop/notes/1979-yalecs-166/yale-166.pdf>: Section 5, the definitions of combined transfer, can·know, rwtg-paths, rw-initial and rw-terminal spans, and the languages $B$ and $C$ (p. 22).
