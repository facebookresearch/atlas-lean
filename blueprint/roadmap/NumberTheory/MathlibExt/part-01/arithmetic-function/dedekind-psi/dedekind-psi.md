---
article_id: af_9bdc9edced2bceca5678f713
declaration: def
origin: cited
statement: formalized
lean: ArithmeticFunction.dedekindPsi
---

# Dedekind Psi

The Dedekind psi function as an arithmetic function taking values in `ℕ`.

For `n = 0` the value is `0`, as required of an arithmetic function. For `n > 0`,
`dedekindPsi n = ∏_{p ^ k ∥ n} p ^ (k - 1) * (p + 1)`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.ArithmeticFunction.DedekindPsi](../../../../../../sources/v2/MathlibExt.md)
