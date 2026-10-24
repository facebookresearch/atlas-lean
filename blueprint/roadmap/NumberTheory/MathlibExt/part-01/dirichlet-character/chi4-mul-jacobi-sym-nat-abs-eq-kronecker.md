---
article_id: af_13c63a858fe44c95dc8b23b5
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.chi4_mul_jacobiSym_natAbs_eq_kroneckerSym_of_odd_of_three_mod_four
---

# Quadratic Reciprocity Three Odd

Reciprocity bridge for `D % 4 = 3` at odd `p`: the Jacobi symbol
needs the `χ₄ p` factor. For `0 < D` the reciprocity sign equals `χ₄ p`;
for `D < 0` the `(-1)` factor supplies it.

## Depends on

- [Kronecker Sym](quadratic/kronecker-sym.md)

## Proof depends on

- [Kronecker At Prime](quadratic/kronecker-at-prime.md)
- [Quadratic Character Aux](kronecker-sym-eq-jacobi-sym-of-prime-ne.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.DirichletCharacter.QuadraticReciprocityThreeOdd](../../../../../sources/v2/MathlibExt.md)
