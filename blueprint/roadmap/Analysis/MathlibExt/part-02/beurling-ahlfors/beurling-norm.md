---
article_id: af_16a920b4086802daf0683754
declaration: def
origin: cited
statement: formalized
lean: MathlibExt.Analysis.BeurlingAhlfors.beurlingNorm
---

# Beurling Norm

The operator norm `‖B‖ₚ`, totalized as the infimum of nonnegative
admissible bound constants in this model. The totalization takes the
value `0` when there is no admissible bound at all, so norm inequalities
alone do not assert boundedness; use `beurlingNorm_le_of_isBound` to
derive them from an actual admissible bound.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Is Bound](is-bound.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.BeurlingAhlfors](../../../../../sources/v2/MathlibExt.md)
