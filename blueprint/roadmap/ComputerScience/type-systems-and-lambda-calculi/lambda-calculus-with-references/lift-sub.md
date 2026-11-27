# Lifting a substitution under a binder

Given a substitution $\sigma$ assigning a term to
each de Bruijn index, its lift is the substitution that sends $0$ to the variable $0$ and each
$x + 1$ to the term $\sigma(x)$ renamed by $n \mapsto n + 1$, that is, with every free variable
raised by one.
