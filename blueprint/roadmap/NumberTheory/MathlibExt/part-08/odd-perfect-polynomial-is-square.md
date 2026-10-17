---
article_id: af_ddff566322b71e618f53fc7b
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.odd_perfect_polynomial_is_square
---

# Odd Perfect Polynomial

Every odd perfect polynomial over `F₂` is a square (Canaday).

Odd means having no linear factor, i.e. coprime to both `X` and `X + 1`;
perfect means equal to the sum of all its divisors. Since every nonzero
polynomial over `F₂` is monic, summing over monic divisors is the full
divisor sum.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.OddPerfectPolynomial](../../../../sources/v2/MathlibExt.md)
- Luis H. Gallardo and Olivier Rahavandrainy, "A Polynomial Variant of Perfect Numbers," Journal of Integer Sequences 23 (2020), Article 20.8.6, Lemma `oddperfect`, lines 155–158 (odd and perfect defined lines 96–108), https://cs.uwaterloo.ca/journals/JIS/VOL23/Gallardo/gallardo7.tex attributed there to Canaday. Proves `Wanted` entry `odd_perfect_polynomial_is_square`.
