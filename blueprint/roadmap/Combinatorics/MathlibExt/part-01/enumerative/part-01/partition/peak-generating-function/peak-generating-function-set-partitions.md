---
article_id: af_e031b826ed0a052bf117241f
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.peak_generating_function_set_partitions
---

# Peak generating function set partitions

For `k ≥ 1`, the generating function `PP_k(x, q)` counting partitions of
`[n]` with `k` blocks by peaks equals the Chebyshev closed form
`x^k (1-q)^k ∏_{j=1}^k (...)`, using Mathlib's second-kind Chebyshev
polynomials evaluated at `t = 1 + x^2 (1-q)/2`. Integer indexing expresses
the source denominator `U_{j-1}(t) - U_{j-2}(t)` directly, including `j = 1`.

Partitions are encoded via restricted-growth strings, with peaks as
strict-rise/strict-descent triples; division is total in the fraction field,
so no nonvanishing hypotheses are part of the formalized statement.

Proof: Following Mansour and Shattuck, Lemmas 2.1, 2.2, and 2.6 and Theorem 2.7,
the proof combines first-occurrence decompositions with the Chebyshev recurrence.

## Depends on

- [Is Surjective Restricted Growth String](is-surjective-restricted-growth-string.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.Partition.PeakGeneratingFunction](../../../../../../../../sources/v2/MathlibExt.md)
- Toufik Mansour and Mark Shattuck, "Counting Peaks and Valleys in a Partition of a Set," Journal of Integer Sequences 13 (2010), Article 10.6.8, Theorem (label th_peak_part), lines 313–317, <https://cs.uwaterloo.ca/journals/JIS/VOL13/Shattuck/shattuck3.tex>.
