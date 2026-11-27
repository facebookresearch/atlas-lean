# Raw normalization produces well-typed terms

Assume equality of base types is
decidable. For every context $\Gamma$ and raw term $t$, if raw normalization of $t$ in $\Gamma$
succeeds with a type $A$ and a raw term $t'$, then the declarative typing judgment
$\Gamma \vdash t' : A$ holds.
