# Type inference for closed expressions

Type inference on an expression $e$ runs
Algorithm W on $e$ in the empty context with fresh-variable counter $0$. If W succeeds with a
substitution $s$, a monotype $\tau$ and a counter $n'$, the inferred type of $e$ is $\tau$;
if W fails, $e$ has no inferred type.
