# Elaboration inverts erasure

Assume equality of base types is decidable. For every
intrinsically typed term $t$ of type $A$ in context $\Gamma$, elaborating the erasure of $t$ in
$\Gamma$ succeeds and returns exactly the pair $(A, t)$. In other words, erasure is a section of
elaboration.
