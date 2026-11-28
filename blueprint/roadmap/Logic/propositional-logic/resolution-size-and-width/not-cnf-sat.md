# A tree-like refutation proves unsatisfiability

A formula with a tree-like derivation of
the empty clause is unsatisfiable.

The same holds for [resolution proofs over clauses given as finite sets of literals](../../proof-theory/resolution/res-proof.md): if the empty clause has such a proof from a finite list of clauses, no assignment satisfies every clause of the list. Enumerating each finite clause as a list turns such a proof into a tree-like derivation of the empty clause, an input clause becoming a leaf and a resolution step a resolution on the same pivot followed by weakening to the enumerated resolvent.
