# Normalization of raw terms

Let the base types have decidable equality. Given a context
$\Gamma$ of simple types and a raw term $r$, raw normalization elaborates $r$ in $\Gamma$. If
elaboration fails, raw normalization fails. If elaboration returns a type $A$ and an
intrinsically typed term $t$ of type $A$, raw normalization returns $A$ together with the
erasure to a raw term of the normal form of $t$ computed by normalization by evaluation.
