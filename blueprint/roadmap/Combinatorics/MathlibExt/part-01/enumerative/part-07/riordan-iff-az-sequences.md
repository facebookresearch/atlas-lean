---
article_id: af_92166e030573050484491461
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.riordan_iff_AZ_sequences
---

# Riordan AZSequences

A- and Z-sequence characterization of ordinary Riordan arrays with integer entries:
a lower-triangular integer matrix is an ordinary Riordan array `g * f ^ k` over the
integers iff it satisfies the `A`-recurrence off the first column and the `Z`-recurrence
in the first column, with rational `A` and `Z`, `A 0 ≠ 0` and the Riordan normalization
`d 0 0 = 1`. The sequences are rational because `A 0 = coeff 1 f` need not be a unit in
`ℤ`.

Correction to the cited source: Barry's Proposition displays the hypothesis
`Z 0 ≠ 0`, but the identity Riordan array has `Z 0 = 0`, so that condition cannot
hold in general. This statement therefore drops `Z 0 ≠ 0` — a deliberate
correction to the source, not just a normalization — and instead imposes the
Riordan normalization `d 0 0 = 1`.

Proof: The forward implication uses coefficientwise triangular expansions in powers of `f`; the
converse reconstructs `g` and `f` from columns zero and one and proves rowwise uniqueness. This is
the route of Barry's Proposition Char following He and Sprugnoli's Theorems 2.1 and 2.2.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.RiordanAZSequences](../../../../../../sources/v2/MathlibExt.md)
- P. Barry, *A Note on a Family of Generalized Pascal Matrices Defined by Riordan Arrays*, Journal of Integer Sequences 16 (2013), Article 13.5.4, Proposition Char, lines 173-180, <https://cs.uwaterloo.ca/journals/JIS/VOL16/Barry2/barry231.tex>, after Theorems 2.1 and 2.2 of He.
