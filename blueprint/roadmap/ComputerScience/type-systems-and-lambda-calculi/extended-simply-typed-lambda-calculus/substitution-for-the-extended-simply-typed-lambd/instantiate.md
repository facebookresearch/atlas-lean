# Instantiating a binder body

Given a term $t$ of type $B$ in $A :: \Gamma$ and a term $a$
of type $A$ in $\Gamma$, the instantiation of $t$ with $a$ is the term of type $B$ in $\Gamma$
obtained by applying to $t$ the single-variable substitution for $a$, which replaces the newest
variable by $a$ and leaves the older variables unchanged.
