# Renaming of PCF terms

Given a renaming $\rho$ from a context $\Gamma$ to a context
$\Delta$, the renaming along $\rho$ of a PCF term of type $A$ in context $\Gamma$ is the term of
type $A$ in context $\Delta$ obtained by replacing each variable $x$ by $\rho(x)$. Under a
$\lambda$-binder, $\rho$ is replaced by its lift, which sends the bound variable to itself and
the successor of each variable $x$ of $\Gamma$ to the successor of $\rho(x)$. Renaming leaves
zero unchanged and commutes with application, successor, predecessor, the zero test and the
fixed-point combinator.
