# Substitution in System T terms

Given a substitution $\sigma$ from $\Gamma$ to $\Delta$,
applying $\sigma$ to a term of type $A$ in context $\Gamma$ gives the term of type $A$ in context
$\Delta$ obtained by replacing each variable $x$ by $\sigma(x)$, with $\sigma$ lifted under a
$\lambda$-binder. Substitution leaves zero unchanged and commutes with application, successor and
the recursor. All variables are replaced simultaneously, and since variables are de Bruijn
indices the substitution is capture-avoiding.
