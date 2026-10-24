---
article_id: af_792d1051d297de4a6ed28c6a
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.BranchValid
---

# Branch Valid

Branch validity: the root-specific head condition applies to the FIRST step
only; every later step is constrained by the adjacent-chain condition over
consecutive pairs. An empty chain means no branch and is valid.

## Depends on

- [Block](block.md)
- [Branch Step](branch-step.md)

## Proof depends on

- [Chain Adj Valid](chain-adj-valid.md)
- [Basic Count](basic-count.md)
- [Branch Bound Exp](branch-bound-exp.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.RestrictedGaussianPartition](../../../../../sources/v2/MathlibExt.md)
