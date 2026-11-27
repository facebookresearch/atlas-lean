# Variables captured by a lambda

For a raw term $b$, the captured variables of $b$ form
the list of free indices of $b$ at binder depth $1$ with duplicates removed: the de Bruijn
indices $j$ such that variable $j + 1$ occurs free in $b$, that is, the free variables of the
abstraction $\lambda.\,b$, each listed once.
