# Closure conversion of a closed term is well scoped

If a source term $t$ is closed (it
has no free variables), then its closure conversion is scoped in $0$: it has no free variables,
and every code body in it is scoped in $1$, so refers only to its parameter.
