# Tellegen's theorem in matrix form

Let `N` and `B` be finite sets of nodes and branches and `A` any real `N × B` matrix. Let `φ` and
`j` be real node potentials and node injections, and `v` and `i` real branch voltages and
currents, such that the voltages come from the potentials, `v = Aᵀ φ`, and the currents balance
the injections, `A i = j`. Then the total branch power equals the total node power:

`v · i = φ · j`.

No sign convention is placed on `A`: the statement applies to the head-positive graph incidence
and to the tail-positive [electrical incidence](../../../../GraphTheory/algebraic-graph-theory/part-01/oriented-incidence-matrices/oriented-incidence.md) alike.

Source: B. D. H. Tellegen, *A general network theorem, with applications*, Philips Research
Reports 7 (1952), 259–269.
