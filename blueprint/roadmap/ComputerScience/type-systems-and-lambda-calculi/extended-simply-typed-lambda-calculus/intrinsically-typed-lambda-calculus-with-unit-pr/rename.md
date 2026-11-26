# Renaming a term of the extended calculus

For a renaming $\rho$ from $\Gamma$ to
$\Delta$, the renaming $t[\rho]$ of a term $t$ of type $A$ in $\Gamma$ is the term of type $A$ in
$\Delta$ defined by recursion on $t$: a variable $x$ becomes $\rho(x)$; under each binder, that
is in the body of an abstraction, in both branches of a case analysis and in the body of a `let`,
the renaming is replaced by its lift; every other former is renamed componentwise.
