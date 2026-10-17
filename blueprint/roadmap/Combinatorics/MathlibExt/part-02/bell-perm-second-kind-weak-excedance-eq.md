---
article_id: af_051fafe93037c46ae78cc086
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.bell_perm_second_kind_weakExcedance_eq_stirlingSecond
---

# Bell Permutations Second Kind

The number of Bell permutations of the second kind over [n] with k weak
excedances equals the Stirling number of the second kind `S(n, k)`.

Zero-based reading of the source's 1-based `[n]`: a restricted growth
function is one where every value below a prefix value has already appeared
in that prefix; the Bell permutation is the product, in increasing index
order, of the swaps `(i, f i)`; a weak excedance is an index with `i ≤ σ i`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.BellPermutationsSecondKind](../../../../sources/v2/MathlibExt.md)
- Fufa Beyene, Jörgen Backelin, Roberto Mantaci, and Samuel A. Fufa, "Set Partitions and Other Bell Number Enumerated Objects," Journal of Integer Sequences 26 (2023), Article 23.1.8, Corollary (label corcycfx), item 1, lines 283–290, https://cs.uwaterloo.ca/journals/JIS/VOL26/Beyene/beyene13.tex
