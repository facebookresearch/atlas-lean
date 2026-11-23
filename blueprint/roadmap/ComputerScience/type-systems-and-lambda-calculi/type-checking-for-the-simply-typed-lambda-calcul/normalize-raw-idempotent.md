# Raw normalization is idempotent

Assume equality of base types is decidable. For every
context $\Gamma$ and raw term $t$, if raw normalization of $t$ in $\Gamma$ succeeds with a type
$A$ and a raw term $t'$, then raw normalization of $t'$ in $\Gamma$ succeeds with the same type
$A$ and the same term $t'$.
