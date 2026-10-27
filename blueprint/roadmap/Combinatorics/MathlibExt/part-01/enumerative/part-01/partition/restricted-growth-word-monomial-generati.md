---
article_id: af_3dbcf64bf9f60a3456108c98
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.restricted_growth_word_monomial_generating_function
---

# Restricted Growth Word Generating Function

The multivariate generating function for restricted-growth words whose largest letter is `k`,
where each variable's exponent is one less than that letter's number of occurrences.

The source letters `1, ..., k` are rendered as `Fin k`; each letter `a` occurs
`d a + 1` times so the word length is `k + d.sum`.

Proof: Decompose restricted-growth words by their first letter to obtain a coefficient
recurrence, lift it to multivariate power series, and iterate Mathlib's power-series inverse
cancellation. The combinatorial route follows Ehrenborg, Hedmark, and Hettle, Theorem 1.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.Partition.RestrictedGrowthWordGeneratingFunction](../../../../../../../sources/v2/MathlibExt.md)
- Richard Ehrenborg, Dustin Hedmark, and Cyrus Hettle, "A Restricted Growth Word Approach to Partitions with Odd/Even Size Blocks," Journal of Integer Sequences 20 (2017), Article 17.5.5, Theorem 1 (label `theorem_one`), lines 190-200, <https://cs.uwaterloo.ca/journals/JIS/VOL20/Ehrenborg/ehren4.tex>.
