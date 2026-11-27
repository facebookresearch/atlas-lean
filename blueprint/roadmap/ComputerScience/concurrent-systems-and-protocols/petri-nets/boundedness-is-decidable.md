# Boundedness of Petri nets is decidable

There is an algorithm that decides, given a [Petri net](place-transition-petri-nets.md) $(N, M_0)$, whether it is [bounded](boundedness-and-safeness.md), and likewise whether it is safe. The coverability tree gives one: the net is bounded if and only if $\omega$ appears in no label of its finite coverability tree. That algorithm can need non-primitive-recursive space, because token generators may have non-primitive-recursive length.

## Depends on

- [Boundedness and safeness of Petri nets](boundedness-and-safeness.md)
- [Place/transition Petri nets](place-transition-petri-nets.md)

## Proof depends on

- [Properties of the coverability tree](decision-procedures/properties-of-the-coverability-tree.md)

## Sources

- J. Esparza and M. Nielsen, "Decidability issues for Petri nets – a survey", BRICS Report Series RS-94-8, Aarhus University, 1994, <https://arxiv.org/abs/2411.01592>, Section 3, paragraph "Boundedness" (Karp and Miller's decidability result and the size of the coverability tree).
- T. Murata, "Petri nets: Properties, analysis and applications", *Proceedings of the IEEE* 77(4):541–580, 1989, Section V-A, property 1) of the coverability tree.
- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, Theorem 3.2.4 and its proof (a breadth-first exploration of the reachability graph that stops at a repeated-and-increased marking), p. 50.
