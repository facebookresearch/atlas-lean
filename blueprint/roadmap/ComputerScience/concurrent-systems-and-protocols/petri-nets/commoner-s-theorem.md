# Commoner's theorem for free-choice nets

Let $(N, M_0)$ be a [free-choice net](subclasses-of-petri-nets.md) whose net is connected and has at least one transition. Then $(N, M_0)$ is [live](liveness-and-deadlock-freedom.md) if and only if every [siphon](siphons-and-traps.md) of $N$ contains a trap that is marked at $M_0$. Both hypotheses, which the survey leaves implicit, are needed for the forward direction: a place with no arcs that is unmarked at $M_0$ is a siphon containing no marked trap, whatever the rest of the net does, and the net consisting of one unmarked place and no transitions is connected and vacuously live.

## Depends on

- [State machines, marked graphs and free-choice nets](subclasses-of-petri-nets.md)
- [Siphons and traps](siphons-and-traps.md)
- [Liveness and deadlock-freedom of Petri nets](liveness-and-deadlock-freedom.md)

## Expansion

This page becomes ready once the two directions are linked to their proof prerequisites:

- for "every siphon contains a marked trap implies live": if the net is not live, some reachable marking $M$ makes every transition either live or dead at $M$ (a transition that is neither can be made dead, and live and dead transitions stay so), with at least one dead; in a free-choice net every transition $t$ dead at $M$ has an input place $s_t$ unmarked at $M$ all of whose input transitions are dead at $M$; the selected places $s_t$, one for each dead transition, form a siphon unmarked at $M$, which contains no trap marked at $M_0$ because a marked trap stays marked (proof prerequisites). The set of all places unmarked at $M$ need not be a siphon.
- for "live implies every siphon contains a marked trap": a live net marks every siphon at $M_0$. For a siphon $R$, let $Q$ be the union of all traps contained in $R$, the largest such set closed under the trap condition, which is empty if $R$ contains no trap, and let $D = R \setminus Q$; it suffices to show that $Q$ is marked at $M_0$, since a marked place of $Q$ lies in a trap contained in $R$. If no transition has an input place in $D$ and $D$ were nonempty, $D \cup Q$ would be a trap contained in $R$ and larger than $Q$, which is impossible; so $D$ is empty and $R = Q$, which is marked because a live net marks every siphon. Otherwise, suppose $Q$ is unmarked at $M_0$. There is a circuit-free allocation of the nonempty set of clusters of the output transitions of $D$ that allocates no input transition of $Q$, and, by the allocation lemma for a nonempty set of clusters, a live free-choice net has an infinite firing sequence that fires allocated transitions infinitely often and the other transitions of those clusters never; along it $Q$ stays unmarked, since a transition that puts a token into $Q \subseteq R$ takes one from $R$, and of the transitions that take from $D$ only allocated ones fire, none of them an input transition of $Q$. In a free-choice net each allocated transition has an input place in $D$. Because the allocation is circuit-free, some allocated transition $t$ that fires infinitely often has an input place $s \in D$ into which no allocated transition firing infinitely often puts a token; from some point on, $s$ is then refilled only by transitions outside the allocated clusters, each of which takes a token from $R$ but not from $D$, hence from $Q$, which is unmarked, a contradiction (proof prerequisites).

## Sources

- T. Murata, "Petri nets: Properties, analysis and applications", *Proceedings of the IEEE* 77(4):541–580, 1989, Section VI-B, Theorem 12 (stated without proof, with Example 9).
- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, Definition 1.3.8 (Petri nets are connected, with nonempty sets of places and transitions) and Theorems 5.3.3 and 5.3.9, whose proofs go through the steps listed under Expansion, pp. 16 and 105–111.
