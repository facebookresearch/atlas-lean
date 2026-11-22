# Extending a PCF substitution by a term

Given a substitution $\sigma$ from a context
$\Gamma$ to a context $\Delta$ and a term $a$ of type $A$ in $\Delta$, the extended substitution
goes from $\Gamma$ extended by a newest variable of type $A$ to $\Delta$: it sends the newest
variable to $a$ and every older variable $x$ of $\Gamma$ to $\sigma(x)$.
