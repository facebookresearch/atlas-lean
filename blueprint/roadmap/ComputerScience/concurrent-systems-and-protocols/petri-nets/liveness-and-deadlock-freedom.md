# Liveness and deadlock-freedom of Petri nets

A [Petri net](place-transition-petri-nets.md) $(N, M_0)$ is *live* if for every marking $M$ in the [reachability set](reachability-set-and-reachability-graph.md) $R(M_0)$ and every transition $t$ there is a firing sequence $M [\sigma\rangle M'$ such that $t$ is enabled at $M'$. It is *deadlock-free* if every reachable marking enables some transition. A transition is *dead* if it is enabled at no reachable marking.

## Depends on

- [Reachability set and reachability graph](reachability-set-and-reachability-graph.md)
- [Place/transition Petri nets](place-transition-petri-nets.md)

## Sources

- T. Murata, "Petri nets: Properties, analysis and applications", *Proceedings of the IEEE* 77(4):541–580, 1989, Section IV-C ("Liveness").
- J. Esparza, "Decidability and complexity of Petri net problems – an introduction", in *Lectures on Petri Nets I: Basic Models*, Lecture Notes in Computer Science 1491, Springer, 1998, pp. 374–428, <https://archive.model.in.tum.de/um/bibdb/esparza/course.pdf>, Sections 2 and 3 (deadlocks, that is markings that enable no transition, and the question whether some reachable marking is one).
