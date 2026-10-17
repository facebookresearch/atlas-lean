---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Logic.PL.Proposition.satisfies_toCNF_iff
---

# Equivalent CNF

**Equivalent CNF**: `A.toCNF ι` is satisfied by `σ` iff `A` is true under `σ ∘ ι`.

## Depends on

- [Satisfies](../semantics/satisfies-3.md)
- [Eval Bool](../../natural-deduction/semantics/eval-bool.md)
- [To CNF](to-cnf.md)

## Proof depends on

- [CNF](../basic/cnf.md)
- [Disj](disj.md)
- [CNFClause](../basic/cnfclause.md)
- [Satisfies](../semantics/satisfies-2.md)
- [Satisfies](../semantics/satisfies.md)
- [Cnf Acc](cnf-acc.md)
- [Cnf Of](cnf-of.md)
- [Cnf Or](cnf-or.md)

## Sources

- [CSLibExt, CSLibExt.Logics.Propositional.CNF.NormalForm](../../../../../../sources/v2/CSLibExt.md)
