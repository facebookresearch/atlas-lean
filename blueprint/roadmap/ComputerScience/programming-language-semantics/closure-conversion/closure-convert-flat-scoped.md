# Flat closure conversion of a closed term is well scoped

If a raw term $t$ is closed,
then its flat closure conversion is scoped in $0$: it has no free variables, and every code
body in it is scoped in $1$, so refers only to its parameter.
