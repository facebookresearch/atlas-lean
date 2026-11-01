---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.TM2Composition.initList_stk_length_le
---

# Init List stk length le

Per-step push budget of a machine. -/
noncomputable def pushBound (M : FinTM2) : ℕ := ∑ l, pushes (M.m l)

theorem length_step (M : FinTM2) (k : M.K) {c c' : M.Cfg} (h : M.step c = some c') :
    (c'.stk k).length ≤ (c.stk k).length + pushBound M := by
  rcases c with ⟨_ | l, v, S⟩
  · simp [FinTM2.step, TM2.step] at h
  · simp only [FinTM2.step, TM2.step] at h
    rw [← Option.some.inj h]
    have hl : pushes (M.m l) ≤ pushBound M :=
      Finset.single_le_sum (f := fun l => pushes (M.m l)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ l)
    exact (length_stepAux k _ v S).trans (Nat.add_le_add_left hl _)

theorem length_iter (M : FinTM2) (k : M.K) :
    ∀ (n : ℕ) (c d : M.Cfg), (flip bind M.step)^[n] (some c) = some d →
      (d.stk k).length ≤ (c.stk k).length + pushBound M * n := by
  intro n
  induction n with
  | zero =>
      intro c d h
      simp only [iterate_zero, id, Option.some.injEq] at h
      subst h; simp
  | succ n ih =>
      intro c d h
      rw [iterate_succ_apply] at h
      change (flip bind M.step)^[n] (M.step c) = some d at h
      cases hc : M.step c with
      | none => rw [hc, TM2Program.iter_none] at h; cases h
      | some c' =>
          rw [hc] at h
          have h₁ := ih c' d h
          have h₂ := length_step M k hc
          rw [Nat.mul_succ]
          omega

/-! ### Monotonicity of `Polynomial ℕ` evaluation -/

theorem eval_mono (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.eval_add]; omega
  | monomial n c =>
      simp only [Polynomial.eval_monomial]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h n)

/-! ### Initial and halting configurations

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Computability.TuringMachine.Composition](../../../../../../sources/v2/MathlibExt.md)
