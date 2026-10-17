---
article_id: af_2970478a18023e5652ef7b61
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.twin_powers
---

# Twin Powers

The Twin Powers theorem relating the B-functions of an odd aeration and its
twin power: with `n = 2 * l + 1`, if either `f = X * g.subst (X ^ n)` or
`h = X * g ^ n` is pseudo-involutory then both are, and
`(X * Bh ^ 2).subst (X ^ n) = (X * P ^ 2).subst (X * Bf ^ 2)` where `P` is the
explicit polynomial built from the coefficients `(2l+1)/(2j+1) * C(l+j, 2j)`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.TwinPowers](../../../../../../sources/v2/MathlibExt.md)
- Alexander Burstein and Louis W. Shapiro, "Pseudo-Involutions in the Riordan Group," Journal of Integer Sequences 25 (2022), Article 22.3.6, The Twin Powers Theorem (label thm:aeration), lines 1129–1146, https://cs.uwaterloo.ca/journals/JIS/VOL25/Burstein/burstein14.tex
