# Lifting a substitution under a binder (simply typed lambda calculus)

Write $A :: \Gamma$
for the context $\Gamma$ extended by a newest variable of type $A$. Given a substitution $\sigma$
from a context $\Gamma$ to a context $\Delta$ and a type $A$, its lift is the substitution from
$A :: \Gamma$ to $A :: \Delta$ that sends the newest variable to the term consisting of the
newest variable alone, and sends the successor of each variable $x$ of $\Gamma$ to the weakening
of the term $\sigma(x)$ into the context $A :: \Delta$.
