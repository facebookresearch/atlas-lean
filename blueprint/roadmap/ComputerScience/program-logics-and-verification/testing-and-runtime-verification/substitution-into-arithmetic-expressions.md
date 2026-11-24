# Substitution of a symbolic store into an arithmetic expression

For a [symbolic store](symbolic-store.md) $\sigma$ and an [arithmetic expression](../../programming-language-semantics/operational-semantics-of-imp/aexp.md) $e$ of IMP, the substitution $\sigma(e)$ replaces every variable $x$ of $e$ by $\sigma(x)$, homomorphically through constants, sums, differences and products.

## Sources

- J. C. King, "Symbolic execution and program testing", *Communications of the ACM* 19(7):385–394, 1976 (symbolic execution, symbolic values and path conditions).
