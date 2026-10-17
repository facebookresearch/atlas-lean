---
article_id: af_ab6206a90532122679e5ca53
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.motzkin_central_trinomial_recurrence
---

# Motzkin central trinomial recurrence

The Motzkin numbers `M` (Catalan-weighted binomial sums) and the canonical
central trinomial coefficients are linked by
`T (n + 1) = T n + 2 * n * M (n - 1)` for `n ≥ 1`. The source attributes the
recurrence to Barcucci, Pinzani, and Sprugnoli, "The Motzkin family" (its
reference PUMA).

Proof: Equation eq1 of Blasiak et al. supplies the central trinomial sum and eq34 supplies the
recurrence. The source uses hybrid-polynomial operator calculus for eq34; here an elementary
termwise binomial identity gives the recurrence.

## Depends on

- [Trinomial Coefficient](../../../../../../NumberTheory/MathlibExt/part-11/trinomial-coefficient.md)

## Proof depends on

- [Trinomial Coefficient self eq sum](trinomial-coefficient-self-eq-sum.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.MotzkinCentralTrinomial](../../../../../../../sources/v2/MathlibExt.md)
- P. Blasiak, G. Dattoli, A. Horzela, K. A. Penson, and K. Zhukovsky, "Motzkin Numbers, Central Trinomial Coefficients and Hybrid Polynomials," Journal of Integer Sequences 11 (2008), Article 08.1.1, Theorem (equation eq34), lines 459–464, https://cs.uwaterloo.ca/journals/JIS/VOL11/Penson/penson131.tex
