# Type safety

Let $S$ be a store typing, $T$ a type, $t$ a term of type $T$ in the
empty variable context under $S$, and $\mu$ a store that is well typed under $S$ in the empty
context. If the configuration $(t, \mu)$ evaluates in zero or more steps to $(t', \mu')$, then
$t'$ is a value or $(t', \mu')$ takes a step to some configuration $(t'', \mu'')$. So a closed
term that is well typed in a well-typed store never reaches a stuck configuration.
