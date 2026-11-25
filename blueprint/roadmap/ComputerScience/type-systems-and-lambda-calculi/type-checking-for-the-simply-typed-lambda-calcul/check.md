# Type checking for raw STLC terms

Assume equality of base types is decidable. Given a
context $\Gamma$ (a list of simple types), a raw term $r$ and a simple type $A$, the type checker
returns true exactly when type inference for $r$ in $\Gamma$ returns the type $A$, and false
otherwise.
