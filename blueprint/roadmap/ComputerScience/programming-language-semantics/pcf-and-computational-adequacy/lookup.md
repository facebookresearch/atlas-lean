# Variable lookup in a PCF environment

For a variable $x$ of type $A$ in a context $\Gamma$,
the lookup of $x$ is the Scott-continuous map from environments for $\Gamma$ to the domain of $A$
defined by recursion on $x$: if $x$ is the newest variable, it sends an environment $(\eta, a)$ to
$a$; if $x$ is the shift of a variable $y$ of the older context, it sends $(\eta, a)$ to the lookup
of $y$ at $\eta$.
