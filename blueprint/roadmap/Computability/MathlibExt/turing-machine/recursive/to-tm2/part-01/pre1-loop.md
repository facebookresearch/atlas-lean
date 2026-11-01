---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.TM2Recursive.pre1_loop
---

# Pre1 loop

Iterated steps of the wrapped machine. -/
noncomputable abbrev frun (j : ℕ) (x : Option (FCfg c)) : Option (FCfg c) :=
  (flip bind (fstep c))^[j] x

theorem frun_add (j₁ j₂ : ℕ) (x : Option (FCfg c)) :
    frun c (j₁ + j₂) x = frun c j₁ (frun c j₂ x) := Function.iterate_add_apply _ _ _ _

theorem frun_succ (j : ℕ) (d : FCfg c) :
    frun c (j + 1) (some d) = frun c j (fstep c d) := Function.iterate_succ_apply _ _ _

theorem frun_zero (x : Option (FCfg c)) : frun c 0 x = x := rfl

theorem frun_one (d : FCfg c) : frun c 1 (some d) = fstep c d := rfl

/-! ### The pre-phase

## Depends on

- [FCfg](fcfg.md)
- [FΓ](f.md)
- [FΛ](f-2.md)
- [Phase](phase.md)
- [Bool ToΓ'](bool-to.md)
- [Frun](frun.md)
- [Mk Stk](mk-stk.md)
- [Supp](supp.md)

## Proof depends on

- [Fstep](fstep.md)
- [Fwd Prog](fwd-prog.md)

## Sources

- [MathlibExt, MathlibExt.Computability.TuringMachine.Recursive.ToTM2](../../../../../../../sources/v2/MathlibExt.md)
