# Lifting a PCF substitution under a binder

Given a substitution $\sigma$ from a context
$\Gamma$ to a context $\Delta$ and a type $A$, the lift of $\sigma$ is the substitution from
$\Gamma$ extended by a newest variable of type $A$ to $\Delta$ extended by a newest variable of
type $A$ that sends the newest variable to the newest variable and every older variable $x$ to
the weakening of $\sigma(x)$ by one variable.
