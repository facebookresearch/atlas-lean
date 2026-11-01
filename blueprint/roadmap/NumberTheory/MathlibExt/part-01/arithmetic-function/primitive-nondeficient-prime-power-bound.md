---
article_id: af_fa9249b7e5027bab7c144c96
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.primitive_nondeficient_prime_power_bound
---

# Primitive Nondeficient Bound

A primitive non-deficient `n` (non-deficient, with all proper divisors
deficient) has a prime factor `p` with `p ^ (v_p(n) + 1) < 2 * k * R`,
where `k` is the number of distinct prime factors and `R` their product.

Here `n.primeFactors.card` is the source's `k`, the product over
`n.primeFactors` is the radical `R`, and `n.factorization p` is the
exponent of `p` in `n`; non-deficiency is `σ(n) ≥ 2n` via `Nat.divisors`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.ArithmeticFunction.PrimitiveNondeficientBound](../../../../../sources/v2/MathlibExt.md)
- Joshua Zelinsky, "Must a Primitive Non-Deficient Number Always Have a Small Component?," Journal of Integer Sequences 29 (2026), Article 26.4.3, Theorem (label maintheoremboundwithkR), equation (label Generalinequalityforprimitivenondeficientnumbers), lines 107–109, https://cs.uwaterloo.ca/journals/JIS/VOL29/Zelinsky/zel14.tex
