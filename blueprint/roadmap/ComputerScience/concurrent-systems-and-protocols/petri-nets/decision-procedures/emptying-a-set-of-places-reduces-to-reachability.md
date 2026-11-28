# Reaching a marking empty on a set of places reduces to reachability

Let $N$ be an ordinary [Petri net](../place-transition-petri-nets.md) whose net is [connected](../state-machines-marked-graphs-and-free-choice-nets/connected-and-strongly-connected-nets.md) and has at least one place and one transition, with places $P$, let $M_0$ be a marking and $R \subseteq P$. Build $N'$ from $N$ by adding places $s_0$ and $r_0$, a transition $t_0$ with input $s_0$ and output $r_0$, arcs from $s_0$ to every transition of $N$ and back, and for every place $s \in P \setminus R$ a transition $t_s$ with inputs $s$ and $r_0$ and output $r_0$; let $M_0'$ extend $M_0$ by one token on $s_0$ and none on $r_0$, and let $M_{r_0}$ be the marking of $N'$ with one token on $r_0$ and no others. Then some marking reachable from $M_0$ in $N$ puts no token on any place of $R$ if and only if $M_{r_0}$ is reachable from $M_0'$ in $N'$.

## Depends on

- [Place/transition Petri nets](../place-transition-petri-nets.md)
- [Reachability set and reachability graph](../reachability-set-and-reachability-graph.md)
- [Connected and strongly connected nets](../state-machines-marked-graphs-and-free-choice-nets/connected-and-strongly-connected-nets.md)

## Sources

- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, Theorem 3.2.26, its construction (Figure 3.4) and facts (1) and (2) of its proof, pp. 67–69.
