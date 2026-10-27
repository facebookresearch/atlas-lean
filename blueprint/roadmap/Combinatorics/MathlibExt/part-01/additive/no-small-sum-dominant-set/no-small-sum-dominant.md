---
article_id: af_009efbfd392462a7559289e5
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.no_small_sum_dominant
---

# No small sum dominant

A set `A` with `|A| < 6` is not sum-dominant.

The source works with sets of nonnegative integers; the hypothesis
`h_nonneg` records the source's normalization and is not needed
(see `card_add_le_card_sub_of_card_lt_six`).

## Depends on

This node has no prerequisites.

## Proof depends on

- [Card add le card sub of card lt six](card-add-le-card-sub-of-card-lt-six.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Additive.NoSmallSumDominantSet](../../../../../../sources/v2/MathlibExt.md)
- Hùng Việt Chu, "When Sets Are Not Sum-Dominant," Journal of Integer Sequences 22 (2019), Article 19.3.7, Theorem (label notsum-dominant), lines 126–128, https://cs.uwaterloo.ca/journals/JIS/VOL22/Chu/chu5.tex
