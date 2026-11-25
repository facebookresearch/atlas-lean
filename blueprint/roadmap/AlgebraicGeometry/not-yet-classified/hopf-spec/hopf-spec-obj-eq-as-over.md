# Hopf Spec obj eq as Over

Mathlib's `hopfSpec` object is the group object on the ordinary spectrum.

This bundled identification carries the group structure across the two instance paths.
Mathlib's operation computation lemmas are stated for `(Spec H).asOver (Spec R)`, while
`hopfSpec` reaches that group object through the Hopf-algebra/cogroup equivalence.
