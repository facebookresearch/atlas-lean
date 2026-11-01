---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Logic.PL.BDD.ofProposition_satPath
---

# Satisfy-one

**Satisfy-one** for propositions: the ROBDD of every proposition over `Nat` atoms has a
satisfying path, and its assignment satisfies the proposition. (Every such proposition is
satisfiable, by the all-true valuation; the path is usually a different model.)

## Depends on

- [Of Path](of-path.md)
- [Of Proposition](../basic/of-proposition.md)
- [Sat Path](sat-path.md)
- [Eval Bool](../../natural-deduction/semantics/eval-bool.md)

## Proof depends on

- [BDD](../basic/bdd.md)
- [Is ROBDD](../basic/is-robdd.md)
- [Ordered From](../basic/ordered-from.md)
- [Reduced](../basic/reduced.md)
- [Apply](../basic/apply.md)
- [Eval](../basic/eval.md)
- [Eval Bool all True](eval-bool-all-true.md)
- [Eval apply](../basic/eval-apply.md)
- [Eval of Path sat Path](eval-of-path-sat-path.md)
- [Of Proposition ne leaf false iff](../basic/of-proposition-ne-leaf-false-iff.md)
- [Ordered From apply](../basic/ordered-from-apply.md)
- [Reduced apply](../basic/reduced-apply.md)
- [Sat Path is Some of ne](sat-path-is-some-of-ne.md)

## Sources

- [CSLibExt, CSLibExt.Logics.Propositional.BDD.Quantify](../../../../../../sources/v2/CSLibExt.md)
