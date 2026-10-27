---
article_id: af_72a5af2d7cadb96926c5ca8e
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.palindromic_compositions_without_two
---

# Palindromic Compositions Without Two

The counts of palindromic compositions without parts equal to `2`, expressed through the
corresponding composition counts, together with their generating function.

`C` counts compositions with no part equal to `2` (with `C m = 0` for `m < 0` and
`C 0 = 1` from the empty composition, matching the source's conventions); `P` counts
the palindromic ones. The generating-function identity `(1 - X^2 - X^3) * P = 1 + X`
is the source's `G_P(z) = (1 + z) / (1 - z^2 - z^3)` cleared of denominators.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.PalindromicCompositionsWithoutTwo](../../../../../../sources/v2/MathlibExt.md)
- Phyllis Chinn and Silvia Heubach, "Integer Sequences Related to Compositions without 2's," Journal of Integer Sequences 6 (2003), Article 03.2.3, Theorem 10 (label `palnums`), lines 462–471, <https://cs.uwaterloo.ca/journals/JIS/VOL6/Heubach/heubach5.tex>.
