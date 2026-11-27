# Simultaneous substitution

Given a substitution $\sigma$ from $\Gamma$ to $\Delta$, the
result $t[\sigma]$ of applying $\sigma$ to a term $t$ of type $A$ in $\Gamma$ is the term of type
$A$ in $\Delta$ defined by recursion on $t$: a variable $x$ becomes $\sigma(x)$; under each
binder, that is in the body of an abstraction, in both branches of a case analysis and in the
body of a `let`, the substitution is replaced by its lift; every other former is substituted
componentwise.
