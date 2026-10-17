---
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.NumberTheory.FiniteSumsFibLucasWanted.add_mul_fibBeta_pow_eq_sum
---

# Theorem 15

**Theorem 15** (corrected multinomial): for `q ≥ 1`
and every real `x`, `(x + qβ)ᵐ` is the sum over `n ≤ m` and
`j₁+⋯+j_q+ℓ₁+⋯+ℓ_q = n` of `√5^{ℓ₁+⋯+ℓ_q} · (n!/(∏jᵢ!∏ℓᵢ!))
· C(m,n) · B_{ℓ₁}⋯B_{ℓ_q} · ∏ F_{jᵢ+1}/(jᵢ+1) · x^{m-n}`,
with the full multinomial coefficient (the paper's displayed
definition omits the `ℓᵢ!` factors, and with them omitted
the identity fails, e.g. at `q = 2`, `x = √5`, `m = 2`).

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.FiniteSumsFibLucasWanted](../../../../../../sources/v2/WantedExt.md)
- Fatima Zohra Bensaci, Rachid Boumahdi, and Laala Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers", Theorem 15.
