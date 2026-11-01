---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Logic.PL.exists_interpolant
---

# Craig interpolation

**Craig interpolation** (semantic form): if every valuation with `⊥` false that makes
`A` true makes `B` true, there is `I` whose atoms are common to `A` and `B` (or `⊥`) with
`A ⊨ I` and `I ⊨ B`.

## Depends on

- [Atoms](atoms.md)
- [Eval Bool](../semantics/eval-bool.md)

## Proof depends on

- [Elim Atoms](elim-atoms.md)
- [Eval Bool congr](eval-bool-congr.md)
- [Eval Bool elim Atoms](eval-bool-elim-atoms.md)
- [Fix Atom](fix-atom.md)

## Sources

- [CSLibExt, CSLibExt.Logics.Propositional.NaturalDeduction.Interpolation](../../../../../../sources/v2/CSLibExt.md)
