---
article_id: af_94166fa40436a12b63a450fe
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.shiftedRiordanArray_constantTerm_and_sumCoefficients
---

# Shifted Riordan Array Row Sums

The constant term and coefficient sum of a shifted Riordan row polynomial: for
the `r`-shifted array, evaluating the row polynomial at 0 gives the column-0
entry `∑ k, A n k * r ^ k`, and evaluating at 1 (the row sum) gives the
column-0 entry of the `(r + 1)`-shifted array.

The `r`-Riordan array is Definition de1parameterRiordan (lines 220–222).
Proves `Wanted` entry `shiftedRiordanArray_constantTerm_and_sumCoefficients`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.ShiftedRiordanArrayRowSums](../../../../../../sources/v2/MathlibExt.md)
- José Agapito, Ângela Mestre, Maria M. Torres, and Pasquale Petrullo, "On One-Parameter Catalan Arrays," Journal of Integer Sequences 18 (2015), Article 15.5.1, Corollary (equations eqColumn0Rr and eqRowsumsRr), lines 240–245, https://cs.uwaterloo.ca/journals/JIS/VOL18/Agapito/agapito2.tex
