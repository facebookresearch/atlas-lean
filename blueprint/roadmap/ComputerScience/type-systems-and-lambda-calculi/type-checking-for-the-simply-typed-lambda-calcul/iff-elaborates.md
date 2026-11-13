# Declarative typing agrees with elaboration

Assume equality of base types is decidable.
For every context $\Gamma$, raw term $t$ and type $A$, the declarative typing judgment
$\Gamma \vdash t : A$ holds if and only if there is an intrinsically typed term $u$ of type $A$
in context $\Gamma$ such that elaborating $t$ in $\Gamma$ succeeds and returns the type $A$
together with $u$.
