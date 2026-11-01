---
article_id: af_71c5f7f2aa2cf2363bbd57de
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.pell_riordan
---

# Pell riordan

The matrix `Pell_k` is the Riordan array `(1/(1-x), x(1+x+⋯+x^k)/(1-x))`:
for `2 ≤ k`, the entries of any matrix satisfying the stated generating-function
relation are the coefficients of the Riordan-array product.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Pell riordan general](pell-riordan-general.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.PellRiordan](../../../../../../../sources/v2/MathlibExt.md)
- Jhon J. Bravo, Jose L. Herrera, and José L. Ramírez, "Combinatorial Interpretation of Generalized Pell Numbers," Journal of Integer Sequences 23 (2020), Article 20.2.1, Theorem (label Riordan), lines 269–272, https://cs.uwaterloo.ca/journals/JIS/VOL23/Bravo/bravo4.tex It follows from `pell_riordan_general`; the hypothesis `hk` is unused and keeps the source's shape. Proves `Wanted` entry `pell_riordan`.
