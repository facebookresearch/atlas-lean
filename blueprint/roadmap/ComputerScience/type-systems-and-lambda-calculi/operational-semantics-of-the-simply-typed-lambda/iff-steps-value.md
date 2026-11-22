# Big-step evaluation is small-step evaluation to a value

For terms $t$ and $v$ of the
same type in the same typing context, $t$ evaluates to $v$ in the big-step semantics, written
$t \Downarrow v$, if and only if $t$ reduces to $v$ in finitely many (possibly zero)
left-to-right call-by-value steps and $v$ is a value, that is, a lambda abstraction.
