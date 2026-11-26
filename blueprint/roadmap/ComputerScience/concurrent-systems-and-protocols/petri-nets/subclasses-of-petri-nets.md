# State machines, marked graphs and free-choice nets

Let $N$ be an ordinary [Petri net](place-transition-petri-nets.md).

- $N$ is a *state machine* if every transition has exactly one input place and exactly one output place.
- $N$ is a *marked graph* if every place has exactly one input transition and exactly one output transition. A marked graph can be drawn as a directed graph whose nodes are the transitions and whose arcs are the places, with tokens on arcs; a *directed circuit* of the net is a directed circuit of this graph, and $M(C)$ is the number of tokens on the circuit $C$ at $M$.
- $N$ is a *free-choice net* if every arc from a place is either the unique outgoing arc of that place or the unique incoming arc of its transition: for every place $p$, $|p^\bullet| \le 1$ or ${}^\bullet(p^\bullet) = \{p\}$.

## Depends on

- [Place/transition Petri nets](place-transition-petri-nets.md)

## Sources

- T. Murata, "Petri nets: Properties, analysis and applications", *Proceedings of the IEEE* 77(4):541–580, 1989, Section VI-A ("Subclass of Petri nets"), items 1)–3), and Section VI-B on the drawing of marked graphs as marked directed graphs.
