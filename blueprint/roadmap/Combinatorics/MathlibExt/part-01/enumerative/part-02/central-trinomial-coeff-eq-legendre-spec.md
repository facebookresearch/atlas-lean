---
article_id: af_e5f280c71775556f0a4f64c5
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.centralTrinomialCoeff_eq_legendre_specialValue
---

# Central Trinomial Legendre

The central trinomial coefficient as a special value of the Legendre
polynomial: `c_n = i^n * √(3^n) * P_n(-i/√3)`.

The standard Legendre value `P_n(-i/√3)` is represented via
`Polynomial.shiftedLegendre`: Mathlib's shifted polynomial satisfies
`P⋆_n(y) = P_n(1 - 2*y)`, so evaluating at `(1 + i/√3)/2` gives `P_n(-i/√3)`.

Proof: Bonnet's recurrence `(n+1) P_{n+1}(x) = (2n+1) x P_n(x) - n P_{n-1}(x)`, evaluated at
`x = -i/√3` and rescaled by `i^n √(3^n)`, becomes the central trinomial recurrence
`(n+1) c_{n+1} = (2n+1) c_n + 3n c_{n-1}` (OEIS A002426), proved in
`MathlibExt.Combinatorics.Enumerative.CentralTrinomialRecurrence`; both sides agree at `n = 0, 1`.

## Depends on

- [Trinomial Coefficient](../../../../../NumberTheory/MathlibExt/part-11/trinomial-coefficient.md)

## Proof depends on

- [Central Trinomial Recurrence](central-trinomial-coeff-three-term-recur.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.CentralTrinomialLegendre](../../../../../../sources/v2/MathlibExt.md)
- P. Blasiak, G. Dattoli, A. Horzela, K. A. Penson, and K. Zhukovsky, "Motzkin Numbers, Central Trinomial Coefficients and Hybrid Polynomials," Journal of Integer Sequences 11 (2008), Article 08.1.1, Proposition with equation `eq20`, lines 337-343, <https://cs.uwaterloo.ca/journals/JIS/VOL11/Penson/penson131.tex>.
