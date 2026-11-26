# Boundedness and safeness of Petri nets

A [Petri net](place-transition-petri-nets.md) $(N, M_0)$ is *$k$-bounded* if $M(p) \le k$ for every place $p$ and every marking $M$ in the [reachability set](reachability-set-and-reachability-graph.md) $R(M_0)$; it is *bounded* if it is $k$-bounded for some $k$, and *safe* if it is $1$-bounded. Since there are finitely many places, a net is bounded exactly when $R(M_0)$ is finite. A marking $M'$ *covers* $M$ if $M' \ge M$ placewise, and the *covering problem* asks whether some reachable marking covers a given marking.

## Depends on

- [Reachability set and reachability graph](reachability-set-and-reachability-graph.md)
- [Place/transition Petri nets](place-transition-petri-nets.md)

## Sources

- T. Murata, "Petri nets: Properties, analysis and applications", *Proceedings of the IEEE* 77(4):541–580, 1989, Section IV-B ("Boundedness").
- J. Esparza, "Decidability and complexity of Petri net problems – an introduction", in *Lectures on Petri Nets I: Basic Models*, Lecture Notes in Computer Science 1491, Springer, 1998, pp. 374–428, <https://archive.model.in.tum.de/um/bibdb/esparza/course.pdf>, Section 8 (the covering and boundedness problems).
