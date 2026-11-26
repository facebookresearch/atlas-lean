# Petri nets are well-structured transition systems

For a [Petri net](../place-transition-petri-nets.md) $N$ with places $P$, the transition system whose states are the markings of $N$, with $M \to M'$ when $M [t\rangle M'$ for some transition $t$, ordered placewise by $\le$ on $\mathbb{N}^P$, is a [well-structured transition system](../../../../Logic/temporal-logic/timed-and-infinite-state-verification/well-structured-transition-systems.md) with strong compatibility: $\le$ is a well-quasi-ordering, and if $M_1 \le M_1'$ and $M_1 [t\rangle M_2$ then $M_1' [t\rangle M_2'$ for some $M_2' \ge M_2$. Its covering problem is the coverability problem of $N$.

## Depends on

- [Place/transition Petri nets](../place-transition-petri-nets.md)
- [Well-structured transition systems](../../../../Logic/temporal-logic/timed-and-infinite-state-verification/well-structured-transition-systems.md)

## Proof depends on

- [Dickson's lemma for finite products of well-quasi-orders](dickson-s-lemma.md)

## Sources

- A. Finkel and Ph. Schnoebelen, "Well-structured transition systems everywhere!", *Theoretical Computer Science* 256(1–2):63–92, 2001, Section 6 ("The well-structure of Petri nets"): the inclusion ordering on markings, Dickson's lemma, and Theorem 6.1, item 1, pp. 76–77.
- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, Definitions 3.2.19 and 3.2.20 and the examples after Definition 3.2.19, pp. 64–65.
