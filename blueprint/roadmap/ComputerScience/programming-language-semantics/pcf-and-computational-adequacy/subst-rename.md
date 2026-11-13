# Substitution after renaming in PCF

Let $\rho$ be a renaming from a context $\Gamma$ to a
context $\Delta$ and $\sigma$ a substitution from $\Delta$ to a context $\Xi$. For every PCF term
$t$ of type $A$ in context $\Gamma$, applying $\sigma$ to the renaming of $t$ along $\rho$ gives
the result of applying to $t$ the substitution from $\Gamma$ to $\Xi$ that sends each variable
$x$ of $\Gamma$ to $\sigma(\rho(x))$.
