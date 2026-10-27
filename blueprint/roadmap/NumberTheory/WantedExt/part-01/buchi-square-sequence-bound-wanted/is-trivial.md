---
article_id: af_da52fcf13b14b06dc61eefd6
declaration: def
origin: cited
statement: formalized
lean: MathlibExt.NumberTheory.BuchiSquareSequenceBoundWanted.IsTrivial
---

# Is Trivial

A length-`M` Büchi sequence is trivial when, up to independently changing
the signs of its terms, it is a run of consecutive increasing integers. Since
independent signs do not change squares, and equality of integer squares
supplies the necessary signs, this is encoded by requiring an integer `x`
with `u j ^ 2 = (x + j) ^ 2` for every `j < M`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.BuchiSquareSequenceBoundWanted](../../../../../sources/v2/WantedExt.md)
