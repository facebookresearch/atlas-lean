---
article_id: af_02d4b1ecaf462830f6e804d6
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.chen_stirlingSecond_expansion
---

# Chen stirling Second expansion

Chen's expansion of the zeroth entry of an array satisfying
`a m (s + 1) = m * a m s - (m + 1) * a (m + 1) s`, a variant of the Akiyama-Tanigawa
algorithm, by signed Stirling numbers of the second kind.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.PolyInitialExpansion](../../../../../../../sources/v2/MathlibExt.md)
- K.-W. Chen, "Algorithms for Bernoulli numbers and Euler numbers," Journal of Integer Sequences 4 (2001), Article 01.1.6, as stated in Dil, Kurt, and Cenkci (2007), Proposition 4. It is the `x = 0` case of `poly_initial_expansion`.
