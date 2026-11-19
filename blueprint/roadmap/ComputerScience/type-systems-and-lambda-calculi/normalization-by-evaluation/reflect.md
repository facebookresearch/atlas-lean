# Reflection of neutral terms

By recursion on the type $A$, simultaneously with [reification](quote.md), every neutral term $n$
of type $A$ in a context $\Gamma$ is reflected as a Kripke semantic value of type $A$ in
$\Gamma$. At a base type the value is $n$ itself. At an arrow type $A \Rightarrow B$ it is the
semantic function that sends a renaming $\rho$ from $\Gamma$ to a context $\Delta$ and a semantic
value $a$ of type $A$ in $\Delta$ to the reflection at $B$ of the neutral term $n'\,q$, where $n'$
is $n$ renamed along $\rho$ and $q$ is the reification of $a$.
