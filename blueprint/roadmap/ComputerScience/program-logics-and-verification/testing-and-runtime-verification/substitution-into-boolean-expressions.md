# Substitution of a symbolic store into a Boolean expression

For a [symbolic store](symbolic-store.md) $\sigma$ and a [Boolean expression](../../programming-language-semantics/operational-semantics-of-imp/bexp.md) $b$ of IMP, the substitution $\sigma(b)$ substitutes $\sigma$ into every arithmetic subexpression, homomorphically through truth values, equality and order tests, negation and conjunction.

## Sources

- J. C. King, "Symbolic execution and program testing", *Communications of the ACM* 19(7):385–394, 1976 (symbolic execution, symbolic values and path conditions).
