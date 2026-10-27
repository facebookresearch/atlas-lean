---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Logic.PL.BDD.ofProposition_ne_leaf_false_iff
---

# Of Proposition ne leaf false iff

A proposition over `Nat` atoms is satisfiable iff its ROBDD is not the leaf `false`.
Both sides always hold (the all-true valuation satisfies every proposition over atoms alone);
`exists_evalBool_eq_false_at_iff` in `Quantify.lean` is the informative version, with one
variable fixed to `false`.

## Depends on

- [BDD](bdd.md)
- [Of Proposition](of-proposition.md)
- [Eval Bool](../../natural-deduction/semantics/eval-bool.md)

## Proof depends on

- [Is ROBDD](is-robdd.md)
- [Ordered From](ordered-from.md)
- [Reduced](reduced.md)
- [Apply](apply.md)
- [Eq leaf false iff](eq-leaf-false-iff.md)
- [Eval](eval.md)
- [Eval apply](eval-apply.md)
- [Ordered From apply](ordered-from-apply.md)
- [Reduced apply](reduced-apply.md)

## Sources

- [CSLibExt, CSLibExt.Logics.Propositional.BDD.Basic](../../../../../../sources/v2/CSLibExt.md)
