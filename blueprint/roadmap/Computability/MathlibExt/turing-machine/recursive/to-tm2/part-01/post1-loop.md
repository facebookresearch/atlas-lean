---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.TM2Recursive.post1_loop
---

# Post1 loop

The pre-phase: from the input configuration to `tr`'s initial configuration on `[n]`. -/
theorem pre_phase (bits : List Bool) :
    frun c (bits.length + 1 + (bits.length + 1) + 1)
        (some ⟨some (Sum.inl Phase.pre0), none, mkStk [] [] [] [] bits []⟩) =
      some ⟨some (Sum.inr ⟨trNormal c Cont'.halt, start_mem c⟩), none,
        mkStk (bits.map boolToΓ' ++ [Γ'.cons]) [] [] [] [] []⟩ := by
  rw [frun_succ]
  have h0 : fstep c ⟨some (Sum.inl Phase.pre0), none, mkStk [] [] [] [] bits []⟩ =
      some ⟨some (Sum.inl Phase.pre1), none, mkStk [Γ'.cons] [] [] [] bits []⟩ := by
    simp [fwdProg, TM2.step, TM2.stepAux, mkStk]
  rw [h0, frun_add, pre1_loop]
  have hlen : bits.length = ((bits.map boolToΓ').reverse ++ []).length := by simp
  rw [hlen, pre2_loop]
  simp

/-! ### The post-phase

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
