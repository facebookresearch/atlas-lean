---
article_id: af_eda201602ac19cd4403ed7b7
declaration: theorem
origin: cited
statement: formalized
lean: MetaMathlibExt.dejean_repetition_threshold
---

# Dejean Repetition Threshold Wanted

Exact values of the repetition threshold `RT(n)` (Dejean's theorem, proved).

Paper: James D. Currie, Lucas Mol, and Narad Rampersad, "The Number of Threshold
Words on n Letters Grows Exponentially for Every n ≥ 27", Journal of Integer
Sequences 23 (2020), Article 20.3.1.

Period/exponent and `r`/`r⁺`-free definitions, lines 93--99, span SHA-256
`b605234e2e71b1ea5528dcca2db0c1f993af359b1e4f7000bd9b0a57c267b639`:
a positive integer `p` is a period of a finite word `w` if `w_{i+p} = w_i`
for all valid `i`, `|w|/p` is an exponent, and a word is `r⁺`-free if it
contains no finite factor of exponent strictly greater than `r`.
Repetition-threshold definition and exact values, lines 100--113, span SHA-256
`0ade39d10ca420a8b8c0b6c56b47e01ab9d40044159ffaf5ae6e6bacb3bce804`:
`RT(n) = inf {r > 1 : there is an infinite r⁺-free word over A_n}` with
`RT(2) = 2`, `RT(3) = 7/4`, `RT(4) = 7/5`, `RT(n) = n/(n-1)` for `n ≥ 5`.
Source file SHA-256
`92a84503716783c6ca89dd1b7e912daa219173ee6083713d539afb4ce706d20e`.

Original definition/conjecture: Françoise Dejean, "Sur un théorème de Thue",
Journal of Combinatorial Theory, Series A 13(1) (1972), 90--99,
DOI 10.1016/0097-3165(72)90011-8.
Final cases confirmed in 2011 by James D. Currie and Narad Rampersad,
"A proof of Dejean's conjecture", Mathematics of Computation 80 (2011),
1063--1070, arXiv:0905.1129, and independently by Michaël Rao,
"Last cases of Dejean's conjecture", Theoretical Computer Science 412(27)
(2011), 3010--3018, DOI 10.1016/j.tcs.2010.06.020.

This is a proved result, recorded here as a Wanted statement (not a conjecture).

Lean representation: `Fin n` harmlessly relabels the source `n`-letter alphabet
`A_n`; the universal period clause (quantifying over starts, positive periods,
factor lengths, and period equations, concluding `(len : ℝ) / (p : ℝ) ≤ r`)
expresses absence of factors with exponent strictly greater than `r`, i.e.
`r⁺`-freeness; `RT` is the real-valued `sInf` over `r > 1` admitting such an
infinite word.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Combinatorics.Words.DejeanRepetitionThresholdWanted](../../../../../sources/v2/WantedExt.md)
- <https://cs.uwaterloo.ca/journals/JIS/VOL23/Mol/mol2.tex>.
