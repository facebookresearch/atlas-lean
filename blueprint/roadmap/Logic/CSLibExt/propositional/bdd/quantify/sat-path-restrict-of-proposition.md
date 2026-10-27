---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Logic.PL.BDD.satPath_restrict_ofProposition
---

# Satisfy-one

**Satisfy-one** with one variable `f` fixed to `false`: if `A` has a model with `f` false,
the cofactor of its ROBDD at `f := false` has a satisfying path, and the path's assignment with
`f` set to `false` is such a model.

## Depends on

- [Of Path](of-path.md)
- [Of Proposition](../basic/of-proposition.md)
- [Restrict](restrict.md)
- [Sat Path](sat-path.md)
- [Eval Bool](../../natural-deduction/semantics/eval-bool.md)

## Proof depends on

- [BDD](../basic/bdd.md)
- [Is ROBDD](../basic/is-robdd.md)
- [Ordered From](../basic/ordered-from.md)
- [Reduced](../basic/reduced.md)
- [Apply](../basic/apply.md)
- [Eval](../basic/eval.md)
- [Eval apply](../basic/eval-apply.md)
- [Eval of Path sat Path](eval-of-path-sat-path.md)
- [Exists eval Bool eq false at iff](exists-eval-bool-eq-false-at-iff.md)
- [Is ROBDD restrict](is-robdd-restrict.md)
- [Mk](../basic/mk.md)
- [Ordered From apply](../basic/ordered-from-apply.md)
- [Reduced apply](../basic/reduced-apply.md)
- [Sat Path is Some of ne](sat-path-is-some-of-ne.md)

## Sources

- [CSLibExt, CSLibExt.Logics.Propositional.BDD.Quantify](../../../../../../sources/v2/CSLibExt.md)
