# Boundedness of Petri nets is decidable

There is an algorithm that decides, given a [Petri net](place-transition-petri-nets.md) $(N, M_0)$, whether it is [bounded](boundedness-and-safeness.md), and likewise whether it is safe. The coverability tree gives one: the net is bounded if and only if $\omega$ appears in no label of its finite coverability tree.

## Depends on

- [Boundedness and safeness of Petri nets](boundedness-and-safeness.md)
- [Place/transition Petri nets](place-transition-petri-nets.md)

## Proof depends on

- [Properties of the coverability tree](properties-of-the-coverability-tree.md)

## Sources

- T. Murata, "Petri nets: Properties, analysis and applications", *Proceedings of the IEEE* 77(4):541–580, 1989, Section V-A, property 1) of the coverability tree.
