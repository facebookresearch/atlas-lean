# Permission algebras and heaps with permissions

Heaps with permissions map locations to value–permission pairs, where permissions combine by a partial commutative and associative operation. Two heaps combine when they agree on the value at every shared location and their permissions there combine, so separating conjunction no longer forces disjoint domains.

A *permission algebra* is a set $P$ with a partial binary operation $\circ$ that is commutative, associative and cancellative, in the sense of the partial equalities of [separation algebras](../abstract-separation-logic/separation-algebras.md). For a set $L$ of locations and a set $V$ of values, a heap with permissions is a partial function $h : L \rightharpoonup V \times P$. Lift $\circ$ to $V \times P$ by $(v, m) \circ (v', m') = (v, m \circ m')$ if $v = v'$ and $m \circ m'$ is defined, and undefined otherwise. Heaps $h, h'$ combine, $h \circ h'$ being defined, if and only if $h(l) \circ h'(l)$ is defined for every $l \in \mathrm{dom}(h) \cap \mathrm{dom}(h')$, and then $(h \circ h')(l)$ is $h(l)$ when $l \notin \mathrm{dom}(h')$, $h'(l)$ when $l \notin \mathrm{dom}(h)$, and $h(l) \circ h'(l)$ otherwise; the empty heap is the unit. The heaps with finite domain form a separation algebra.

A *write permission* of such a model is a distinguished $m_W \in P$ that combines with nothing:

$$m_W \circ m' \text{ is undefined for every } m' \in P.$$

Each concrete model names its write permission ([fractional and counting permission models](fractional-and-counting-permission-models.md)).

For a store $s$ and expressions $E, E'$, the permission-annotated points-to assertion is

$$s, h \models E \overset{m}{\mapsto} E' \iff \mathrm{dom}(h) = \{[\![E]\!]s\} \text{ and } h([\![E]\!]s) = ([\![E']\!]s, m),$$

and separating conjunction splits a heap $h$ as $h = h_0 \circ h_1$. In the sequential heap language the atomic commands keep their usual semantics plus run-time permission checks: mutation $[E'] := E$ and disposal $\mathrm{dispose}(E')$ require the addressed cell to carry exactly $m_W$ and fault otherwise, lookup $x := [E']$ succeeds with any permission and leaves the heap unchanged, and allocation $x := \mathrm{new}(E)$ creates a fresh cell holding the value of $E$ with permission $m_W$.

## Depends on

- [Separation algebras](../abstract-separation-logic/separation-algebras.md)

## Proof depends on

None.

## Expansion

The lifting and the points-to are those of the permission-accounting paper, which states them over a partial commutative semigroup of permissions; the cancellative presentation, in which finite heaps form a separation algebra, is that of abstract separation logic. Maximality of the write permission means that a heap holding $m_W$ for a cell admits no frame mentioning that cell, which is what keeps mutation and disposal safety monotone and framing. The store-and-heap semantics of the other assertions is the standard one of separation logic.

## Sources

- R. Bornat, C. Calcagno, P. O'Hearn and M. Parkinson, "Permission accounting in separation logic", *Proceedings of the 32nd ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL 2005)*, ACM, 2005, pp. 259–270, <https://doi.org/10.1145/1040305.1040327>, author copy <http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/permissions_paper.pdf>, Section 10.1 (heaps over a permission structure, the lifted operation, condition (14) on the write permission, the annotated points-to) and Section 11.1 (the semantics (19) of atomic commands with permission checks).
- C. Calcagno, P. W. O'Hearn and H. Yang, "Local action and abstract separation logic", *Proceedings of the 22nd Annual IEEE Symposium on Logic in Computer Science (LICS 2007)*, IEEE, 2007, pp. 366–378, <https://doi.org/10.1109/LICS.2007.30>, author copy <https://www.cs.ox.ac.uk/people/hongseok.yang/paper/asl-short.pdf>, Section 2, example 2 after Definition 1 (permission algebras and heaps with permissions).
