# Instantiating a binder body (simply typed lambda calculus)

Write $A :: \Gamma$ for the
context $\Gamma$ extended by a newest variable of type $A$. Given a term $t$ of type $B$ in
context $A :: \Gamma$ and a term $a$ of type $A$ in context $\Gamma$, the instantiation of $t$
with $a$ is the term of type $B$ in context $\Gamma$ obtained by applying to $t$ the
single-variable substitution for $a$, which replaces the newest variable by $a$ and leaves the
older variables unchanged.
