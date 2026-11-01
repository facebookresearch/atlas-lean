---
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.NumberTheory.Recurrences.ABFibonacciIdentitiesWanted.sum_neg_one_pow_jacobsthal
---

# Theorem 10(d)

**Theorem 10(d)**: the Jacobsthal case
`(a, b) = (1, 2)` (`J` and `j` in the paper):
`∑ (-1)^i 2^(n-i) J_{2i} = ((-1)^n j_{2n+1} - 2^n) / 9`,
`∑ (-1)^i 2^(n-i) j_{2i} = (-1)^n J_{2n+1} + 2^n`,
`∑ (-1)^i 2^(n-i) J_{2i+1} = ((-1)^n j_{2n+2} + 2^(n+2)) / 9`,
`∑ (-1)^i 2^(n-i) j_{2i+1} = (-1)^n J_{2n+2}`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.Recurrences.ABFibonacciIdentitiesWanted](../../../../../../sources/v2/WantedExt.md)
- Emil Daniel Schwab, "Fibonacci Numbers via Dirichlet Convolution and Lucas Numbers via Unitary Convolution", Theorem 10(d).
