---
article_id: af_6639ab6a282a7b7fb9830a6b
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.IsConwayHofstadterLikeSequence
---

# Is Conway Hofstadter Like Sequence

A Conway–Hofstadter-like sequence of order `k`.

For `n ≥ 3`, the two recursive indices add to `n`. The helper
`conwayHofstadterResidue` implements the source's explicit convention that residue zero modulo
`n - 1` is written as `n - 1`, rather than as zero.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Conway Hofstadter Residue](conway-hofstadter-residue.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.ConwayHofstadterLikeSequence](../../../../../sources/v2/MathlibExt.md)
