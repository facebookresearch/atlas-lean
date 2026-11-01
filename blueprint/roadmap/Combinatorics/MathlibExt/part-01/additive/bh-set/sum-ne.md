---
article_id: af_64257600ce83416da1ee3e95
declaration: def
origin: cited
statement: formalized
lean: AdditiveCombinatorics.sumNE
---

# Sum NE

Sum of the entries of a nonempty list, by folding `+` over the tail starting
from the head. The `l ≠ []` hypothesis rules out the empty list; it is ignored
by the computation, so it cannot affect the value
(see `sumNE_proof_irrel`).

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Additive.BhSet](../../../../../../sources/v2/MathlibExt.md)
