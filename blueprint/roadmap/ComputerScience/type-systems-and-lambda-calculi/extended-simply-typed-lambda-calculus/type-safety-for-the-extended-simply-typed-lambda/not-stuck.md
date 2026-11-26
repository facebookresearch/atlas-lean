# Closed terms never reach a stuck term

If $t$ is a term of type $A$ in the empty context
and $t$ reduces in any number of call-by-value steps to $t'$, then $t'$ is not stuck: it is not
the case that $t'$ is a normal form of `Step` and not a value.
