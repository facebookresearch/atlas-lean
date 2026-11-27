# Closed terms reduce only to values or reducible terms

If $t$ is a term of type $A$ in
the empty context and $t$ reduces in any number of call-by-value steps to $t'$, then $t'$ is a
value or reduces further. The proof applies progress at $t'$, which has type $A$ because
reduction preserves types by construction.
