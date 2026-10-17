---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Logic.PL.CNFClause.satisfies_restrict_iff
---

# Satisfies restrict iff

In a clause not already made true by `literal`, deleting the assigned
variable preserves satisfaction by an assignment extending `literal`.

## Depends on

- [CNFClause](../basic/cnfclause.md)
- [Satisfies](../semantics/satisfies-2.md)
- [Restrict](restrict.md)

## Proof depends on

- [Satisfies](../semantics/satisfies.md)

## Sources

- [CSLibExt, CSLibExt.Logics.Propositional.CNF.Restriction](../../../../../../sources/v2/CSLibExt.md)
