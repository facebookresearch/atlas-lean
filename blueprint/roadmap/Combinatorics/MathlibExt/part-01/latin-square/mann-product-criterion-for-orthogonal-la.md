---
article_id: af_d72ddae8147f96ea02d7d2a7
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.mann_product_criterion_for_orthogonal_latin_squares
---

# Mann

Mann's product criterion: for two order-`n` Latin squares `A` and `B`,
their overlay is bijective if and only if the rowwise product `A B⁻¹` is a
Latin square.

The two column hypotheses are retained to express that the inputs are Latin
squares, although the equivalence itself only uses the row bijectivity
hypotheses. The row clause on the right is likewise automatic from those row
hypotheses, but is included so that the right side states the full Latin-square
condition.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.LatinSquare.Mann](../../../../../sources/v2/MathlibExt.md)
