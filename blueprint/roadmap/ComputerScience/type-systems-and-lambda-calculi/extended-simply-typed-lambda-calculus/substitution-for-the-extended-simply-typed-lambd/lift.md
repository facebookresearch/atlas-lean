# Lifting a substitution under a binder

Given a substitution $\sigma$ from $\Gamma$ to
$\Delta$ and a type $A$, its lift is the substitution from $A :: \Gamma$ to $A :: \Delta$ that
sends the newest variable to the term consisting of the newest variable alone, and sends the
successor of each variable $x$ of $\Gamma$ to the weakening of $\sigma(x)$ into $A :: \Delta$.
