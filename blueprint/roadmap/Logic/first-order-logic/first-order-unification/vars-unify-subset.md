# Unification introduces no new variables

Let $E$ be a list of equations between terms.
If the unification algorithm succeeds on $E$ and returns the substitution $s$, then for every
variable $x$, each variable of the term $s(x)$ is either $x$ itself or a variable occurring in
some equation of $E$.
