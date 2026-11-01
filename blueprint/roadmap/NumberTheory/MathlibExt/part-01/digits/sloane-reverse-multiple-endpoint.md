---
article_id: af_6fbc2f4601d2e98110ed21b4
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.sloane_reverse_multiple_endpoint
---

# Sloane Reverse Multiple

Sloane reverse-multiple endpoint formula: a `(g, k)` reverse multiple in
little-endian digits with endpoint sum `a₀ + aLast = g` satisfies
`(k + 1) * aLast = g`, so `aLast = g / (k + 1)` and `k + 1 ∣ g`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Digits.SloaneReverseMultiple](../../../../../sources/v2/MathlibExt.md)
- L. H. Kendrick, *Young Graphs: 1089 et al.*, Journal of Integer Sequences 18 (2015), Article 15.9.7, Corollary `cor:lastdig1089` (Sloane's Conjecture 3.5) and proof, lines 418–424, <https://cs.uwaterloo.ca/journals/JIS/VOL18/Kendrick/ken1.tex>. Proves `Wanted` entry `sloane_reverse_multiple_endpoint`.
