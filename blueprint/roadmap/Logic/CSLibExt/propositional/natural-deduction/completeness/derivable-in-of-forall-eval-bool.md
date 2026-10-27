---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Logic.PL.Theory.derivableIn_of_forall_evalBool
---

# Strong completeness

**Strong completeness** of natural deduction for classical theories: a sequent true
under every valuation that reads `⊥` as false and satisfies `T` is `T`-derivable.

## Depends on

- [Eval Bool](../semantics/eval-bool.md)

## Proof depends on

- [Bool Satisfiable](bool-satisfiable.md)
- [Eval Bool neg](../semantics/eval-bool-neg.md)
- [Consistent With](consistent-with.md)
- [Model existence](bool-satisfiable-2.md)

## Sources

- [CSLibExt, CSLibExt.Logics.Propositional.NaturalDeduction.Completeness](../../../../../../sources/v2/CSLibExt.md)
