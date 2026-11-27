# Finite-state CTL model checking by structural recursion

The set of states of a finite labelled transition system that satisfy a CTL formula, computed by
structural recursion on the formula: atoms by filtering the valuation, $\mathsf{EX}\,\varphi$ as
the set of states with a successor in the set for $\varphi$, $\mathsf{E}[\varphi\, \mathsf{U}\, \psi]$
and $\mathsf{EG}\,\varphi$ as fixed points reached by finite iteration, and
$\mathsf{A}[\varphi\, \mathsf{U}\, \psi]$ through its duality with the existential operators applied
to the complements of the sets for the subformulas, adjusted for states without successors by
means of the set of states that have a successor.
