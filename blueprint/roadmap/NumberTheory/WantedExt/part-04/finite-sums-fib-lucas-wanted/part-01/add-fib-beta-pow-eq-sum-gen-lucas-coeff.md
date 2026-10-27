---
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.NumberTheory.FiniteSumsFibLucasWanted.add_fibBeta_pow_eq_sum_genLucasCoeff
---

# Theorem 11

**Theorem 11** (corrected): `(x + β)ᵐ = (1/(2√5))
∑_{n=0}^m C(m,n) cₙ x^{m-n}` where `cₙ` is
`genLucasCoeff n`, the printed inner sum
`∑_{k=0}^n √5ᵏ C(n,k) Gₖ L_{n-k+1}/(n-k+1)` plus the
dropped term `2√5^{n+1} G_{n+1}/(n+1)` (the printed form
already fails at `m = 0`, giving `0` for `1`).

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.FiniteSumsFibLucasWanted](../../../../../../sources/v2/WantedExt.md)
- Fatima Zohra Bensaci, Rachid Boumahdi, and Laala Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers", Theorem 11.
