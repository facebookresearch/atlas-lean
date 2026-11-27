# Place/transition Petri nets

A *Petri net* is a 5-tuple $(P, T, F, W, M_0)$ where $P$ and $T$ are finite disjoint sets of places and transitions with $P \cup T \ne \emptyset$, $F \subseteq (P \times T) \cup (T \times P)$ is the set of arcs, $W : F \to \{1, 2, 3, \dots\}$ is the weight function, and $M_0 : P \to \mathbb{N}$ is the initial marking; $N = (P, T, F, W)$ is the net and $(N, M_0)$ the marked net. A *marking* is a map $M : P \to \mathbb{N}$. Write $w(p, t)$ and $w(t, p)$ for the weights of the arcs from $p$ to $t$ and from $t$ to $p$, taken to be $0$ when there is no such arc, and ${}^\bullet x$ and $x^\bullet$ for the sets of input and output nodes of a node $x$. A net is *ordinary* if every arc has weight $1$.

A transition $t$ is *enabled* at $M$ if $M(p) \ge w(p, t)$ for every input place $p$ of $t$. An enabled transition may fire, and firing $t$ at $M$ yields the marking $M'$ with $M'(p) = M(p) - w(p, t) + w(t, p)$ for every place $p$, written $M [t\rangle M'$. A *firing sequence* $\sigma = t_1 t_2 \cdots t_n$ from $M$ is a sequence with $M [t_1\rangle M_1 [t_2\rangle \cdots [t_n\rangle M_n$, written $M [\sigma\rangle M_n$.

## Sources

- T. Murata, "Petri nets: Properties, analysis and applications", *Proceedings of the IEEE* 77(4):541–580, 1989, Section II and Table 2 (the formal definition and the firing rule), and Section IV-A (firing sequences).
- J. Esparza and M. Nielsen, "Decidability issues for Petri nets – a survey", BRICS Report Series RS-94-8, Aarhus University, 1994, <https://arxiv.org/abs/2411.01592>, Section 2 (nets, markings, occurrence sequences; ordinary nets, where every arc has weight one).
