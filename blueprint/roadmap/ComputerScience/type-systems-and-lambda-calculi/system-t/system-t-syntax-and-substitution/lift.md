# Lifting a substitution under a binder

Given a substitution $\sigma$ from $\Gamma$ to
$\Delta$ and a type $A$, the lift of $\sigma$ goes from $\Gamma$ extended by a newest variable of
type $A$ to $\Delta$ extended by a newest variable of type $A$: it sends the newest variable to
the newest variable and every older variable $x$ to the weakening of $\sigma(x)$.
