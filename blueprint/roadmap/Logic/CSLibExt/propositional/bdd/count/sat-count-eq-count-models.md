---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Logic.PL.BDD.satCount_eq_countModels
---

# Satisfy-count

**Satisfy-count**: for a diagram ordered from `0` whose variables are below `m`,
`satCount m t` is the number of assignments to `0, …, m - 1` that make it true.

## Depends on

- [BDD](../basic/bdd.md)
- [Ordered From](../basic/ordered-from.md)
- [Vars LT](vars-lt.md)
- [Count Models](count-models.md)
- [Eval](../basic/eval.md)
- [Sat Count](sat-count.md)

## Proof depends on

- [Sat Count From](sat-count-from.md)
- [Sat Count From eq count Models](sat-count-from-eq-count-models.md)

## Sources

- [CSLibExt, CSLibExt.Logics.Propositional.BDD.Count](../../../../../../sources/v2/CSLibExt.md)
