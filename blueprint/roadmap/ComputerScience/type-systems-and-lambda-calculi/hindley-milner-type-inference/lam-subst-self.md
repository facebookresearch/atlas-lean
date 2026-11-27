# Substitution stops at a binder of the same name

For all expressions $e$ and $v$ and
every name $x$, $(\lambda x.\, e)[x := v] = \lambda x.\, e$: an abstraction that binds $x$ has no
free occurrence of $x$.
