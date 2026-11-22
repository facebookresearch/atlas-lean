# Renaming then substituting an intrinsically typed STLC term

Let $\rho$ be a renaming from
the typing context $\Gamma$ to the typing context $\Delta$, $\sigma$ a substitution from $\Delta$
to the typing context $\Xi$, and $t$ a term of type $A$ in context $\Gamma$. Renaming $t$ by
$\rho$ and then applying $\sigma$ gives the same term as applying to $t$ the substitution that
sends each variable $x$ of $\Gamma$ to $\sigma(\rho(x))$.
