# Renaming a simply typed term

For a renaming $\rho$ from a context $\Gamma$ to a context
$\Delta$, the renaming $t[\rho]$ of a term $t$ of type $A$ in context $\Gamma$ is the term of
type $A$ in context $\Delta$ defined by recursion on $t$: $x[\rho] = \rho(x)$ for a variable
$x$, $(f\,a)[\rho] = f[\rho]\,a[\rho]$ for an application, and
$(\lambda s)[\rho] = \lambda (s[\rho^{\uparrow}])$ for an abstraction, where $\rho^{\uparrow}$
is the lift of $\rho$ under one binder.
