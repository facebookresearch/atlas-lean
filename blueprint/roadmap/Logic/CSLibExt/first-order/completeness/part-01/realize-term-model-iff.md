---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Logic.FOL.realize_termModel_iff
---

# Truth lemma

**Truth lemma.** If `Δ` has a witness for every universal formula, then a formula holds in
the term model under `x ↦ [x]` iff it is in `Δ`.

## Depends on

- [Natural deduction](../../natural-deduction/derivable.md)
- [Symm](../../natural-deduction/symm.md)
- [Trans](../../natural-deduction/trans.md)
- [Maximal Consistent](../../consistency/maximal-consistent.md)
- [Func update](func-update.md)
- [Mem of provable](../../consistency/mem-of-provable.md)
- [Rel update](rel-update.md)
- [Provable](../../natural-deduction/provable.md)
- [Term Model](term-model.md)
- [Instantiate](../../syntax/instantiate.md)
- [Term Assignment](term-assignment.md)
- [Term Setoid](term-setoid.md)
- [Term Structure](term-structure.md)
- [Update chain](update-chain.md)

## Proof depends on

- [Consistent](../../consistency/consistent.md)
- [Instantiate mem of all mem](../../consistency/instantiate-mem-of-all-mem.md)
- [Not mem iff](../../consistency/not-mem-iff.md)
- [Mp](../../consistency/mp.md)
- [Depth](depth.md)
- [Instantiate Term](../../syntax/instantiate-term.md)
- [Lower Term](lower-term.md)
- [Realize all formula](../../syntax/realize-all-formula.md)
- [Realize instantiate formula](../../syntax/realize-instantiate-formula.md)

## Sources

- [CSLibExt, CSLibExt.Logics.FirstOrder.Completeness](../../../../../../sources/v2/CSLibExt.md)
