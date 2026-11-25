# Type inference for raw terms

Assume equality of base types is decidable. Given a
context $\Gamma$ and a raw term $t$, type inference elaborates $t$ in $\Gamma$; if elaboration
succeeds, it returns the type component of the result and forgets the intrinsically typed term,
and if elaboration fails, inference fails.
