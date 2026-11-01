---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Logic.PL.BDD.exists_evalBool_eq_false_at_iff
---

# Exists eval Bool eq false at iff

Satisfiability with one variable `f` fixed to `false` (for instance a variable that
plays the role of falsum): `A` has such a model iff the cofactor of its ROBDD at `f := false`
is not the leaf `false`. Without such a constraint, every proposition over `Nat` atoms is
satisfied by the all-true valuation.

## Depends on

- [BDD](../basic/bdd.md)
- [Of Proposition](../basic/of-proposition.md)
- [Restrict](restrict.md)
- [Eval Bool](../../natural-deduction/semantics/eval-bool.md)

## Proof depends on

- [Is ROBDD](../basic/is-robdd.md)
- [Ordered From](../basic/ordered-from.md)
- [Reduced](../basic/reduced.md)
- [Apply](../basic/apply.md)
- [Eq leaf false iff](../basic/eq-leaf-false-iff.md)
- [Eval](../basic/eval.md)
- [Eval apply](../basic/eval-apply.md)
- [Is ROBDD restrict](is-robdd-restrict.md)
- [Mk](../basic/mk.md)
- [Ordered From apply](../basic/ordered-from-apply.md)
- [Reduced apply](../basic/reduced-apply.md)

## Sources

- [CSLibExt, CSLibExt.Logics.Propositional.BDD.Quantify](../../../../../../sources/v2/CSLibExt.md)
