# Full β-reduction in the locally nameless STLC is safe

A closed term of type `τ` reduces
in any number of full β-steps only to values or to terms that reduce further. Full β-reduction
reduces under binders, so a value can still step; the statement is at the level of relations,
with values as the final states, and is not a statement about the anchor `OpSem`, whose final
states must be terminal.
