---
article_id: af_bdf0045490999455d3f01822
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.stirlingFirst_addition
---

# Stirling First Addition

Addition formula for the unsigned Stirling numbers of the first kind.

The source sums `j, i = 0, …, v`; the `if j ≤ k` guard encodes the
vanishing of the factor `[u; k-j]` for `j > k`, and `u.ascFactorial i`
is the source's rising factorial `u^{(i)}`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.StirlingFirstAddition](../../../../../../sources/v2/MathlibExt.md)
- Grzegorz Rządkowski, "Two Formulas for Successive Derivatives and Their Applications," Journal of Integer Sequences 12 (2009), Article 09.8.2, Theorem, equation (ex44), lines 257–263, https://cs.uwaterloo.ca/journals/JIS/VOL12/Rzadkowski/rzadkowski3.tex
