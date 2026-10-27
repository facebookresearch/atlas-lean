---
article_id: af_de4f7f6ff7dd3ba2102bb334
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: GenContFract.of_den_succ_lt_succ_succ
---

# Approximations

Successive denominators of a regular continued fraction are strictly
increasing after the initial denominator, provided the next partial
denominator exists.

This isolates the prerequisite used in arXiv:2607.23662, source item
`2607.23662:D07`. The paper uses `q_(k-1) < q_k` rather than stating this
universal form verbatim. The shift is necessary because `dens 0 = 1`, while
`dens 1` can also equal `1`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Algebra.ContinuedFractions.Computation.Approximations](../../../../../sources/v2/MathlibExt.md)
