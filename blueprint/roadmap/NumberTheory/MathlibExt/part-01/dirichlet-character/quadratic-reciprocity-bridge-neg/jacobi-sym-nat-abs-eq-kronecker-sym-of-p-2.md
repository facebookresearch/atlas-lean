---
article_id: af_25b78d0d217f7bdf82ebb69d
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.jacobiSym_natAbs_eq_kroneckerSym_of_prime_ne_two_of_one_mod_four
---

# Jacobi Sym nat Abs eq kronecker Sym of prime ne two of one mod four

Combined reciprocity bridge for `D % 4 = 1` at an odd prime `p`.
Covers every `D ≡ 1 (mod 4)`, of either sign: the `0 < D` case and
the `D < 0` case (`D = 0` is impossible since `(0 : ℤ) % 4 = 0`).
`h1` is a genuine truth condition, not a proof boundary: at
`(D, p) = (3, 7)` the left side is `1` while the right side is `-1`.
The `D = 4 * m` family remains uncovered.

## Depends on

- [Kronecker Sym](../quadratic/kronecker-sym.md)

## Proof depends on

- [Jacobi Sym nat Abs eq kronecker Sym of prime ne two of one mod four neg](jacobi-sym-nat-abs-eq-kronecker-sym-of-p.md)
- [Quadratic Reciprocity Bridge](../jacobi-sym-nat-abs-eq-kronecker-sym-of-p.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.DirichletCharacter.QuadraticReciprocityBridgeNeg](../../../../../../sources/v2/MathlibExt.md)
