---
article_id: af_9cc7d75628373279243785eb
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.Convex.ChoquetWanted.choquet_representation
---

# Choquet representation

For a nonempty compact convex `K` in a second-countable real Banach space, every `x ∈ K` is the
Bochner barycenter of a Borel probability measure carried by the extreme points: there exists `μ`
with `μ (extremePoints ℝ K) = 1`, integrable `y ↦ y`, and `∫ y dμ = x`. Source: G. Choquet,
Seminaire Bourbaki 1956 and Lectures 1962; Bishop-de Leeuw and Choquet-Bishop-de Leeuw integral
representation; Phelps, Lectures on Choquet's Theorem, 1966; Lean states compact-source
specialization in second-countable real Banach space with `ProbabilityMeasure` carried by
`extremePoints` and Bochner integral barycenter.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Choquet representation of is Compact](choquet-representation-of-is-compact.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.Convex.Choquet](../../../../../../sources/v2/MathlibExt.md)
