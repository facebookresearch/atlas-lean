---
article_id: af_6571fce6129651164c0d5cd3
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Combinatorics.Matroid.MatroidIntersectionWanted.edmonds_matroid_intersection'
---

# Edmonds matroid intersection'

Edmonds matroid intersection min-max for finite matroids on a finite type, with no assumption on
the ground sets: there is a common independent set of size at least `k` iff every cut `X`
satisfies `k ≤ M₁.eRk X + M₂.eRk Xᶜ`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Exists common indep of cut le](exists-common-indep-of-cut-le.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Matroid.MatroidIntersection](../../../../../../sources/v2/MathlibExt.md)
