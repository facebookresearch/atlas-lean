# De facto rules and admissible rw-paths

Let $G_0$ be a [protection graph](take-grant-protection-graphs.md). Besides its explicit edges, a graph may carry *implicit* edges labelled $r$, which record a
potential flow of information that is not an access right. The four *de facto rules* each add an implicit edge from $x$ to $z$ labelled $r$, where $x, y, z$ are
distinct vertices and "edge" means an explicit or implicit edge:

- **Post:** $x$ and $z$ are subjects, the edge from $x$ to $y$ contains $r$ and the edge from $z$ to $y$ contains $w$;
- **Pass:** $y$ is a subject, the edge from $y$ to $x$ contains $w$ and the edge from $y$ to $z$ contains $r$;
- **Spy:** $x$ and $y$ are subjects, the edge from $x$ to $y$ contains $r$ and the edge from $y$ to $z$ contains $r$;
- **Find:** $y$ and $z$ are subjects, the edge from $y$ to $x$ contains $w$ and the edge from $z$ to $y$ contains $w$.

For distinct vertices $p, q$, $\mathrm{can{\cdot}know{\cdot}f}(p, q, G_0)$ holds if there are graphs $G_1, \dots, G_n$ ($n \ge 0$), each obtained from the previous one by a
de facto rule, such that $G_n$ has an edge from $p$ to $q$ labelled $r$.

An *rw-path* is a sequence of distinct vertices $v_0, \dots, v_k$ with $k > 1$ such that $v_i$ and $v_{i+1}$ are joined by an edge, in either direction, whose label
contains $r$ or $w$; its associated words over $\{\vec r, \overleftarrow r, \vec w, \overleftarrow w\}$ record the label and direction of each edge as for
[tg-paths](tg-paths-islands-spans-and-bridges.md). The rw-path is *admissible* if it has an associated word $a_1 a_2 \cdots a_k$ in $(\vec r \cup \overleftarrow w)^*$ such that
$v_{i-1}$ is a subject whenever $a_i = \vec r$ and $v_i$ is a subject whenever $a_i = \overleftarrow w$.

## Depends on

- [Take–grant protection graphs](take-grant-protection-graphs.md)
- [tg-paths, islands, spans and bridges](tg-paths-islands-spans-and-bridges.md)

## Sources

- M. Bishop and L. Snyder, *The Transfer of Information and Authority in a Protection System*, Research Report 166, Department of Computer Science, Yale University, July 1979, <http://nob.cs.ucdavis.edu/~bishop/notes/1979-yalecs-166/yale-166.pdf>: Section 2 (implicit edges and the rules Post, Pass, Spy and Find, pp. 6–8) and Section 3 (can·know·f, rw-paths and admissible rw-paths, pp. 12–13).
