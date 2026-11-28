# Extended free-choice nets

Let $N$ be an ordinary [Petri net](../place-transition-petri-nets.md) with places $P$, transitions $T$ and arcs $F$. $N$ is *extended free-choice* if ${}^\bullet t \times s^\bullet \subseteq F$ for every arc $(s, t) \in F$ from a place to a transition: whenever $s$ is an input place of $t$, every input place of $t$ is an input place of every output transition of $s$. Equivalently, for all transitions $t_1 \ne t_2$, ${}^\bullet t_1 \cap {}^\bullet t_2 \ne \emptyset$ implies ${}^\bullet t_1 = {}^\bullet t_2$; equivalently, for all places $s_1 \ne s_2$, $s_1^\bullet \cap s_2^\bullet \ne \emptyset$ implies $s_1^\bullet = s_2^\bullet$. Every [free-choice net](../subclasses-of-petri-nets.md) is extended free-choice, since there $s_1^\bullet \cap s_2^\bullet \ne \emptyset$ forces $|s_1^\bullet| = |s_2^\bullet| = 1$.

## Depends on

- [Place/transition Petri nets](../place-transition-petri-nets.md)
- [State machines, marked graphs and free-choice nets](../subclasses-of-petri-nets.md)

## Sources

- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, Definition 5.3.1 (free-choice nets in the sense of these notes) and Proposition 5.3.2 (alternative definitions), pp. 104–105.
- T. Murata, "Petri nets: Properties, analysis and applications", *Proceedings of the IEEE* 77(4):541–580, 1989, Section VI-A, items 3) and 4) (free-choice and extended free-choice nets, with the equivalent form of the free-choice condition) and Fig. 25(f).
