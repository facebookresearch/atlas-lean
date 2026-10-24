---
article_id: af_bf7570a65e1419a999719f53
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.exists_isPrimitiveDivisor_fib
---

# Fibonacci Primitive Divisor

Fibonacci corollary of Carmichael's theorem, as invoked in Haojie Hong,
*On big primitive divisors of Fibonacci numbers*, arXiv:2312.04354v1,
`bigPFn.tex` lines 153–158 (<https://arxiv.org/abs/2312.04354>):
with `α = (1+√5)/2`, `β = (1-√5)/2` and `uₙ = Fₙ = Nat.fib n` (so `(α-β)² = 5`),
`Fₙ` has a primitive divisor for `n ≥ 7` and `n ≠ 12`, i.e. there exists a
prime `p` such that `LucasSequence.IsPrimitiveDivisor (fun k => (Nat.fib k : Int)) 5 n p`.
This is the Fibonacci specialization of Carmichael's broader theorem on general
Lucas sequences (R. D. Carmichael, *On the numerical factors of the arithmetic
forms αⁿ±βⁿ*, Ann. of Math. (2) 15 (1913), 30–70).

## Depends on

- [Primitive Divisor](../part-02/is-primitive-divisor.md)

## Proof depends on

- [Padic Val Nat fib mul](../../../part-01/padics/fibonomial-prime-power-valuation/padic-val-nat-fib-mul.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Recurrences.FibonacciPrimitiveDivisor](../../../../../../sources/v2/MathlibExt.md)
