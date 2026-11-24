# Type renaming preserves typing

Let $\Gamma$ be a term context with $m$ term variables over $n$ type variables, $t \in \mathrm{Tm}_{n,m}$ a term and $A \in \mathrm{Ty}_n$ a type with $\Gamma \vdash t : A$ ([typing](typing.md)). For every renaming $\rho : \{0, \dots, n - 1\} \to \{0, \dots, k - 1\}$ of type variables, $\Gamma\langle\rho\rangle \vdash t\langle\rho\rangle : A\langle\rho\rangle$, where $\rho$ [renames](../scoped-pure-system-f/rename.md) every type of $\Gamma$, the [type variables of $t$](../scoped-pure-system-f/ty-rename.md) and $A$; no term variable is added.
