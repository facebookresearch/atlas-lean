# Reachability set and reachability graph

In a [Petri net](place-transition-petri-nets.md) $(N, M_0)$, a marking $M$ is *reachable* from $M_0$ if $M_0 [\sigma\rangle M$ for some firing sequence $\sigma$. The *reachability set* $R(N, M_0)$, or $R(M_0)$, is the set of markings reachable from $M_0$, and $L(N, M_0)$ is the set of firing sequences from $M_0$. The *reachability graph* is the labelled directed graph whose nodes are the reachable markings, with an edge labelled $t$ from $M$ to $M'$ whenever $M [t\rangle M'$. The *reachability problem* asks, given $(N, M_0)$ and a marking $M$, whether $M \in R(N, M_0)$.

## Depends on

- [Place/transition Petri nets](place-transition-petri-nets.md)

## Sources

- T. Murata, "Petri nets: Properties, analysis and applications", *Proceedings of the IEEE* 77(4):541–580, 1989, Section IV-A ("Reachability").
- J. Esparza and M. Nielsen, "Decidability issues for Petri nets – a survey", BRICS Report Series RS-94-8, Aarhus University, 1994, <https://arxiv.org/abs/2411.01592>, Section 2 (reachable markings and the reachability graph) and Section 3 (the reachability problem).
