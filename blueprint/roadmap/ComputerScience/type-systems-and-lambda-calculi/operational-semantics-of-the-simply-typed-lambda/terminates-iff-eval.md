# Termination in terms of big-step evaluation

For every closed term $t$ of type $A$, that
is, a term in the empty typing context, $t$ terminates (it reduces to a value in finitely many
left-to-right call-by-value steps) if and only if there is a term $v$ such that $t$ evaluates to
$v$ in the big-step semantics, written $t \Downarrow v$.
