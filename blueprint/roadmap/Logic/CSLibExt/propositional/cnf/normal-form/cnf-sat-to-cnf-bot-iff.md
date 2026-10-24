---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Logic.PL.Proposition.cnfSat_toCNF_bot_iff
---

# Cnf Sat to CNF bot iff

With the atom `⊥` read as false: adding the unit clause `¬⊥` gives a CNF that is
satisfiable iff `A` has a model with `⊥` false.

## Depends on

- [CNFClause](../basic/cnfclause.md)
- [CNFSat](../basic/cnfsat.md)
- [Eval Bool](../../natural-deduction/semantics/eval-bool.md)
- [To CNF](to-cnf.md)

## Proof depends on

- [CNF](../basic/cnf.md)
- [Satisfies](../semantics/satisfies-3.md)
- [Satisfies](../semantics/satisfies-2.md)
- [Equivalent CNF](satisfies-to-cnf-iff.md)
- [Cnf Sat iff exists satisfies](../semantics/cnf-sat-iff-exists-satisfies.md)

## Sources

- [CSLibExt, CSLibExt.Logics.Propositional.CNF.NormalForm](../../../../../../sources/v2/CSLibExt.md)
