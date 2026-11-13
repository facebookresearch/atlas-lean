# Type inference is sound and complete

Assume equality of base types is decidable. For
every context $\Gamma$, raw term $t$ and type $A$, type inference for $t$ in $\Gamma$ returns
$A$ if and only if the declarative typing judgment $\Gamma \vdash t : A$ holds.
