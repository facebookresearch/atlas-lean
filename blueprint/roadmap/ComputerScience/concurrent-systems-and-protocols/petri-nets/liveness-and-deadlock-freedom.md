# Liveness and deadlock-freedom of Petri nets

A [Petri net](place-transition-petri-nets.md) $(N, M_0)$ is *live* if for every marking $M$ in the [reachability set](reachability-set-and-reachability-graph.md) $R(M_0)$ and every transition $t$ there is a firing sequence $M [\sigma\rangle M'$ such that $t$ is enabled at $M'$. It is *deadlock-free* if every reachable marking enables some transition. A transition is *dead* if it is enabled at no reachable marking.

## Depends on

- [Reachability set and reachability graph](reachability-set-and-reachability-graph.md)
- [Place/transition Petri nets](place-transition-petri-nets.md)

## Sources

- T. Murata, "Petri nets: Properties, analysis and applications", *Proceedings of the IEEE* 77(4):541–580, 1989, Section IV-C ("Liveness").
- J. Esparza and M. Nielsen, "Decidability issues for Petri nets – a survey", BRICS Report Series RS-94-8, Aarhus University, 1994, <https://arxiv.org/abs/2411.01592>, Section 3 ("Liveness" and "Deadlock-freedom").
