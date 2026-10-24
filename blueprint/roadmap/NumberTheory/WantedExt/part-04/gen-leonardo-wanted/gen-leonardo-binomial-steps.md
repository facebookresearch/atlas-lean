---
declaration: theorem
origin: cited
statement: formalized
lean: MetaMathlibExt.genLeonardo_binomial_steps
---

# Gen Leonardo binomial steps

The step-3 and step-4 binomial identities:
`∑_i C(n,i) L_{k,3i+r} = 2^n L_{k,2n+r}`,
`∑_i C(n,i) M_{k,3i+r} = 2^n M_{k,2n+r}`,
`∑_i C(n,i) L_{k,4i+r} = 3^n L_{k,2n+r} + k (3^n - 2^n)`, and
`∑_i C(n,i) M_{k,4i+r} = 3^n M_{k,2n+r} + 2k (3^n - 2^n)`
(part (iv) as printed in the paper shows `k (3^n - 2^n)`, which is
false at `k = n = 1, r = 0`; the factor `2k` used here is verified
computationally, consistent with parts (ii) of Theorems 3.1–3.3).

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.GenLeonardoWanted](../../../../../sources/v2/WantedExt.md)
- Kuhapatanakul, *Note on the Generalized Leonardo Numbers*, Fibonacci Quarterly (2024), Theorem 3.4 (`fq-2024-kuhapatanakul05292024-thm-3.4`).
