# Extension of a simply typed substitution

Given a term $a$ of type $A$ in a context
$\Delta$ and a substitution $\sigma$ from $\Gamma$ to $\Delta$, the extension of $\sigma$ by $a$ is
the substitution from the context $\Gamma$ extended by a newest variable of type $A$ to $\Delta$
that sends the newest variable to $a$ and each older variable $x$ of $\Gamma$ to $\sigma(x)$.
