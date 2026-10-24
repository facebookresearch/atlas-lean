---
article_id: af_8114e3e0e1cf662cc792083d
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.golomb_like_closed_form
---

# Golomb Like Sequence

Closed form for Golomb-like solutions of `f (f n) = y * n + z`.

The source's opposite-parity hypothesis is `y % 2 ≠ z % 2`; the
constants `c_1` and `c_2` of the source are expanded inline.

Proof: The construction tiles the positive integers by the source's blocks and verifies the
two slope regimes, followed by strong-induction uniqueness, as in Cloitre–Sloane–Vandermast,
Theorem Th1 and equations (Eq48a), (Eq48).

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Recurrences.GolombLikeSequence](../../../../../../sources/v2/MathlibExt.md)
- Benoit Cloitre, N. J. A. Sloane, and Matthew J. Vandermast, "Numerical Analogues of Aronson's Sequence," Journal of Integer Sequences 6 (2003), Article 03.2.2, Theorem (label Th1), equations (Eq48a) and (Eq48), lines 584–603, https://cs.uwaterloo.ca/journals/JIS/VOL6/Cloitre/cloitre2.tex
