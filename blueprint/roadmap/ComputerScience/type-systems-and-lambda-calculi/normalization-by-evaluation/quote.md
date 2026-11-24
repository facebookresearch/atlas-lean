# Reification of semantic values

By recursion on the type $A$, simultaneously with [reflection](reflect.md), every Kripke semantic
value $v$ of type $A$ in a context $\Gamma$ is reified as a normal form of type $A$ in $\Gamma$.
At a base type, $v$ is a neutral term and its reification is $v$ as a normal form. At an arrow
type $A \Rightarrow B$, the reification is $\lambda t$, where $t$ is the reification at $B$ of $v$
applied, along the weakening renaming from $\Gamma$ into the context $\Gamma$ extended by $A$, to
the reflection at $A$ of the new variable.
