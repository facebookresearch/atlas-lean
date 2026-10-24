---
article_id: af_a3d4c45f5773f3d64be32277
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Probability.McDiarmid.mcdiarmid_one_sided_finite_iid
---

# Mcdiarmid one sided finite iid

Finite iid McDiarmid inequality gives exponential tail bound above the mean.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Mcdiarmid one sided finite iid general](mcdiarmid-one-sided-finite-iid-general.md)
- [Mcdiarmid one sided finite iid of sum sq eq zero](mcdiarmid-one-sided-finite-iid-of-sum-sq.md)

## Sources

- [MathlibExt, MathlibExt.Probability.McDiarmid](../../../../../sources/v2/MathlibExt.md)
- C. McDiarmid, Surveys in Combinatorics 1989, 148-188, DOI 10.1017/CBO9781107359949.008. When every `c i` is `0` (including `n = 0`), the right-hand side is `Real.exp 0 = 1` by Lean's convention `x / 0 = 0`; `mcdiarmid_one_sided_finite_iid_of_sum_sq_eq_zero` gives the sharp value `prob = 0` there, and `mcdiarmid_one_sided_finite_iid_general` covers `0 < ∑ i, c i ^ 2`. The instance `[DecidableEq α]` is unused and keeps the source's shape. Proves `Wanted` entry `mcdiarmid_one_sided_finite_iid`.
