---
article_id: af_896fcec034c8208b8fe08f27
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Probability.BerryEsseenWanted.berry_esseen_explicit
---

# Berry esseen explicit

I.i.d. Berry–Esseen bound with explicit constant `42`.

Reusable public API for `berry_esseen`: the constant is stated explicitly, and
the redundant `Integrable (X 0) P` premise is omitted since it follows from
`hXmem` via `MemLp.integrable` on a probability space.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Berry esseen finset Sum gaussian](berry-esseen-finset-sum-gaussian.md)

## Sources

- [MathlibExt, MathlibExt.Probability.BerryEsseen](../../../../../sources/v2/MathlibExt.md)
