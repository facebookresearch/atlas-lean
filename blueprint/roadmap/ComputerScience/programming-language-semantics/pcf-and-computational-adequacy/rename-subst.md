# Renaming after substitution in PCF

Let $\sigma$ be a substitution from a context $\Gamma$
to a context $\Delta$ and $\rho$ a renaming from $\Delta$ to a context $\Xi$. For every PCF term
$t$ of type $A$ in context $\Gamma$, renaming along $\rho$ the result of applying $\sigma$ to $t$
gives the result of applying to $t$ the substitution from $\Gamma$ to $\Xi$ that sends each
variable $x$ of $\Gamma$ to the renaming of $\sigma(x)$ along $\rho$.
