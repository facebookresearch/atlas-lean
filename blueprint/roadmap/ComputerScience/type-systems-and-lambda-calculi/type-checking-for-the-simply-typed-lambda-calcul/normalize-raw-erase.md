# Raw normalization of an erased term

Assume equality of base types is decidable. For
every intrinsically typed term $t$ of type $A$ in context $\Gamma$, raw normalization of the
erasure of $t$ in $\Gamma$ succeeds and returns the type $A$ together with the erasure of the
normal form of $t$ computed by normalization by evaluation.
