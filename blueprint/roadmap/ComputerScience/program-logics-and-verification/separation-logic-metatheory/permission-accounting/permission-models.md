# Permission algebras and heaps with permissions

Heaps with permissions map locations to value–permission pairs, where permissions combine by a partial commutative and associative operation. Two heaps combine when they agree on the value at every shared location and their permissions there combine, so separating conjunction no longer forces disjoint domains.

A *permission algebra* is a set $P$ with a partial binary operation $\circ$ that is commutative, associative and cancellative, in the sense of the partial equalities of [separation algebras](../abstract-separation-logic/separation-algebras.md). For a set $L$ of locations and a set $V$ of values, a heap with permissions is a partial function $h : L \rightharpoonup V \times P$. Lift $\circ$ to $V \times P$ by $(v, m) \circ (v', m') = (v, m \circ m')$ if $v = v'$ and $m \circ m'$ is defined, and undefined otherwise. Heaps $h, h'$ combine, $h \circ h'$ being defined, if and only if $h(l) \circ h'(l)$ is defined for every $l \in \mathrm{dom}(h) \cap \mathrm{dom}(h')$, and then $(h \circ h')(l)$ is $h(l)$ when $l \notin \mathrm{dom}(h')$, $h'(l)$ when $l \notin \mathrm{dom}(h)$, and $h(l) \circ h'(l)$ otherwise. The empty heap $\emptyset$ is a unit for this combination.

Heaps form a separation algebra when the permissions are the non-unit shares of a separation algebra of shares. Let $(S, \oplus)$ be a separation algebra with unit $u_S$ in which $x \oplus y = u_S$ implies $x = y = u_S$, and let $S^+ = S \setminus \{u_S\}$; by cancellativity $u_S$ is the only element with $x \oplus x = x$. Then the heaps $h : L \rightharpoonup V \times S^+$, combined as above with $\circ = \oplus$ restricted to $S^+$, form a separation algebra with unit $\emptyset$: a location absent from a heap plays the part of the unit share, and no occupied cell carries it.

A *write permission* of such a model is a distinguished $m_W \in P$ that combines with nothing:

$$m_W \circ m' \text{ is undefined for every } m' \in P.$$

Each concrete model names its write permission ([fractional and counting permission models](fractional-and-counting-permission-models.md)).

For a store $s$ and expressions $E, E'$, the permission-annotated points-to assertion is

$$s, h \models E \overset{m}{\mapsto} E' \iff \mathrm{dom}(h) = \{[\![E]\!]s\} \text{ and } h([\![E]\!]s) = ([\![E']\!]s, m),$$

and separating conjunction splits a heap $h$ as $h = h_0 \circ h_1$. In the sequential heap language the atomic commands keep their usual semantics plus run-time permission checks: mutation $[E'] := E$ and disposal $\mathrm{dispose}(E')$ require the addressed cell to carry exactly $m_W$ and fault otherwise, lookup $x := [E']$ succeeds with any permission and leaves the heap unchanged, and allocation $x := \mathrm{new}(E)$ creates a fresh cell holding the value of $E$ with permission $m_W$.

## Depends on

- [Separation algebras](../abstract-separation-logic/separation-algebras.md)

## Proof depends on

- [Separation algebras](../abstract-separation-logic/separation-algebras.md)

## Expansion

Cancellativity of the permissions alone does not make the heaps cancellative. On $P = \{R, RW\}$ let the only defined product be $R \circ R = R$; this operation is commutative, associative and cancellative, and $RW$ combines with nothing. For the one-cell heap $h = [\ell \mapsto (v, R)]$ the lifting gives $h \circ \emptyset = h = h \circ h$, while $\emptyset \neq h$. The share construction excludes exactly this situation: an element with $x \oplus x = x$ is the unit share, which never occurs in an occupied cell, and the condition that non-units never join to the unit keeps the combination of occupied cells inside $S^+$. The fractional permissions $(0, 1]$ and the counting permissions $\mathbb{Z}$ are the non-unit shares of the fractional and counting share models, so heaps over them are separation algebras.

The lifting and the points-to are those of the permission-accounting paper, stated there over a partial commutative semigroup of permissions. This page uses only its exclusion law (14) for the write permission; it does not adopt the paper's further condition (15) on extending permissions to the write permission. Maximality of the write permission means that a heap holding $m_W$ for a cell admits no frame mentioning that cell, which is what keeps mutation and disposal safety monotone and framing. The store-and-heap semantics of the other assertions is the standard one of separation logic.

## Sources

- R. Bornat, C. Calcagno, P. O'Hearn and M. Parkinson, "Permission accounting in separation logic", *Proceedings of the 32nd ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL 2005)*, ACM, 2005, pp. 259–270, <https://doi.org/10.1145/1040305.1040327>, author copy <http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/permissions_paper.pdf>, Section 10.1 (heaps over a permission structure, the lifted operation, the exclusion law (14), the annotated points-to) and Section 11.1 (the semantics (19) of atomic commands with permission checks).
- C. Calcagno, P. W. O'Hearn and H. Yang, "Local action and abstract separation logic", *Proceedings of the 22nd Annual IEEE Symposium on Logic in Computer Science (LICS 2007)*, IEEE, 2007, pp. 366–378, <https://doi.org/10.1109/LICS.2007.30>, author copy <https://www.cs.ox.ac.uk/people/hongseok.yang/paper/asl-short.pdf>, Section 2, example 2 after Definition 1 (permission algebras, heaps with permissions, and the permission algebra $\{R, RW\}$ with $R \circ R = R$).
- R. Dockins, A. Hobor and A. W. Appel, "A fresh look at separation algebras and share accounting", *Programming Languages and Systems (APLAS 2009)*, LNCS 5904, Springer, 2009, pp. 161–177, <https://doi.org/10.1007/978-3-642-10672-9_13>, author copy dated June 2009 <https://www.cs.princeton.edu/~appel/papers/fresh-sa.pdf>, Section 3, Definition 6 (the lifting operator, which removes the units), Section 5 (the positivity axiom (22)–(23) assumed of every separation algebra) and Section 6, equations (33) and (34) (heaps as partial functions to pairs of non-unit shares and values, and their points-to).
