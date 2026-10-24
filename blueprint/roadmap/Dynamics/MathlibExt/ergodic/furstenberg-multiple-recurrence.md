---
article_id: af_60c3ff2061f6e44aff666f99
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Dynamics.Ergodic.MultipleRecurrenceWanted.furstenberg_multipleRecurrence
---

# Multiple Recurrence

If `T` preserves a probability measure `μ` and `A` is measurable with `0 < μ A`, then for every `k
> 0` there exists `n > 0` such that `⋂ i ∈ Finset.range k, T^[i * n] ⁻¹' A` has positive measure.

Proof: We apply the finitary Szemerédi theorem to dense sets of return times in finite orbit
segments, using an averaging argument to obtain a positive-measure family of such segments.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Szemeredi](../../../Combinatorics/MathlibExt/part-01/additive/szemeredi.md)

## Sources

- [MathlibExt, MathlibExt.Dynamics.Ergodic.MultipleRecurrence](../../../../sources/v2/MathlibExt.md)
- H. Furstenberg, J. Analyse Math. 31 (1977) and Recurrence in Ergodic Theory (1981); Lean states one-transformation arithmetic-progression k-term intersection form without ergodicity hypothesis.
