# Left-to-right reduction of argument lists

An argument list steps, in a class table, by two rules. Head step: if an expression $e$ [steps](step.md) to $e'$, then the list $e, \bar a$ steps to $e', \bar a$, with the tail unchanged. Tail step: if $v$ is a [value](value.md) and the list $\bar a$ steps to $\bar a'$, then $v, \bar a$ steps to $v, \bar a'$. So the list steps at its leftmost entry that is not a value; a head that is neither a value nor able to step blocks the entries after it (E-CONTEXT).
