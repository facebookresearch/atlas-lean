---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Logic.PL.exists_interpolant_cpl
---

# Craig interpolation

**Craig interpolation** for classical natural deduction: if `CPL` derives `A → B`, there
is `I` over the atoms common to `A` and `B` (and `⊥`) with `CPL` deriving `A → I` and
`I → B`.

## Depends on

- [Atoms](atoms.md)

## Proof depends on

- [Eval Bool](../semantics/eval-bool.md)
- [Completeness for truth tables](../completeness/derivable-in-cpl-iff.md)
- [Craig interpolation](exists-interpolant.md)

## Sources

- [CSLibExt, CSLibExt.Logics.Propositional.NaturalDeduction.Interpolation](../../../../../../sources/v2/CSLibExt.md)
