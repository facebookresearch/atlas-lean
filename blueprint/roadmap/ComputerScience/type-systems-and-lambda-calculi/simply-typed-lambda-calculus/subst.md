# Simultaneous substitution (simply typed lambda calculus)

Given a substitution $\sigma$
from a context $\Gamma$ to a context $\Delta$, the result $t[\sigma]$ of applying $\sigma$ to a
term $t$ of type $A$ in context $\Gamma$ is the term of type $A$ in context $\Delta$ defined by
recursion on $t$: $x[\sigma] = \sigma(x)$ for a variable $x$,
$(f\,a)[\sigma] = f[\sigma]\,a[\sigma]$ for an application, and
$(\lambda u)[\sigma] = \lambda\,(u[\sigma'])$ for an abstraction with body $u$, where
$\sigma'$ is the lift of $\sigma$ under the binder. Because variables are de Bruijn indices, this
substitution is capture-avoiding.
