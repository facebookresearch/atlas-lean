# Small-step evaluation to a value implies big-step evaluation

Let $t$ and $v$ be terms of
the same type in the same typing context. If $t$ reduces to $v$ in finitely many (possibly zero)
left-to-right call-by-value steps and $v$ is a value, then $t$ evaluates to $v$ in the big-step
semantics, written $t \Downarrow v$.
