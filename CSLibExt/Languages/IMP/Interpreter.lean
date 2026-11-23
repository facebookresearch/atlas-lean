/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Fuelled evaluation for IMP
-/
module

public import CSLibExt.Languages.IMP.BigStep

/-!
# Fuelled IMP evaluation

`exec` interprets IMP commands with fuel bounding recursive
derivation depth. Fuel `0` always fails; at fuel `k + 1` every
recursive call runs with fuel `k`. `none` reports fuel exhaustion
only, never divergence.
-/

@[expose] public section

namespace Cslib.IMP

/-- Total fuelled evaluator for IMP commands.

Fuel bounds recursive derivation depth: `0` returns `none` for every
command, and at `k + 1` each recursive call receives fuel `k` (both
sequence children and both while unfoldings share the full `k`).
`none` means only fuel exhaustion for this evaluator, not a proof
that the command diverges. -/
def exec : Nat → Cmd → State → Option State
  | 0, _, _ => none
  | _ + 1, .skip, s => some s
  | _ + 1, .assign name value, s =>
      some (Function.update s name (value.eval s))
  | k + 1, .seq first second, s =>
      match exec k first s with
      | none => none
      | some m => exec k second m
  | k + 1, .ite guard thenBranch elseBranch, s =>
      if guard.eval s then exec k thenBranch s else exec k elseBranch s
  | k + 1, .while guard body, s =>
      if guard.eval s then
        match exec k body s with
        | none => none
        | some m => exec k (.while guard body) m
      else
        some s

/-- Fuel `0` fails for every command: `none` records fuel exhaustion,
not divergence. -/
@[simp]
theorem exec_zero {c : Cmd} {s : State} : exec 0 c s = none := by
  simp [exec]

/-- At positive fuel, `skip` returns the input state. -/
@[simp]
theorem exec_skip {k : Nat} {s : State} :
    exec (k + 1) .skip s = some s := by
  simp [exec]

/-- At positive fuel, assignment updates the named variable. -/
@[simp]
theorem exec_assign {k : Nat} {name : Nat} {value : AExp}
    {s : State} :
    exec (k + 1) (.assign name value) s =
      some (Function.update s name (value.eval s)) := by
  simp [exec]

/-- A sequence fails when its first child exhausts fuel. -/
theorem exec_seq_none {k : Nat} {first second : Cmd} {s : State}
    (h : exec k first s = none) :
    exec (k + 1) (.seq first second) s = none := by
  simp [exec, h]

/-- A sequence runs its second child after a successful first child,
both with the same predecessor fuel. -/
theorem exec_seq_some {k : Nat} {first second : Cmd} {s m : State}
    (h : exec k first s = some m) :
    exec (k + 1) (.seq first second) s = exec k second m := by
  simp [exec, h]

/-- An `ite` with a true guard runs its then-branch. -/
theorem exec_ite_true {k : Nat} {guard : BExp}
    {thenBranch elseBranch : Cmd} {s : State}
    (h : guard.eval s = true) :
    exec (k + 1) (.ite guard thenBranch elseBranch) s =
      exec k thenBranch s := by
  simp [exec, h]

/-- An `ite` with a false guard runs its else-branch. -/
theorem exec_ite_false {k : Nat} {guard : BExp}
    {thenBranch elseBranch : Cmd} {s : State}
    (h : guard.eval s = false) :
    exec (k + 1) (.ite guard thenBranch elseBranch) s =
      exec k elseBranch s := by
  simp [exec, h]

/-- A `while` with a false guard returns the input state. -/
theorem exec_while_false {k : Nat} {guard : BExp} {body : Cmd}
    {s : State} (h : guard.eval s = false) :
    exec (k + 1) (.while guard body) s = some s := by
  simp [exec, h]

/-- A `while` with a true guard fails when its body exhausts fuel. -/
theorem exec_while_true_none {k : Nat} {guard : BExp} {body : Cmd}
    {s : State} (hg : guard.eval s = true)
    (hb : exec k body s = none) :
    exec (k + 1) (.while guard body) s = none := by
  simp [exec, hg, hb]

/-- A `while` with a true guard reruns itself after a successful body,
both with the same predecessor fuel. -/
theorem exec_while_true_some {k : Nat} {guard : BExp} {body : Cmd}
    {s m : State} (hg : guard.eval s = true)
    (hb : exec k body s = some m) :
    exec (k + 1) (.while guard body) s =
      exec k (.while guard body) m := by
  simp [exec, hg, hb]

/-- Soundness: a successful fuelled execution witnesses a canonical
`BigStep` derivation for the same command and states. -/
theorem exec_sound {fuel : Nat} {c : Cmd} {s t : State}
    (h : exec fuel c s = some t) : BigStep c s t := by
  revert c s t
  induction fuel with
  | zero =>
      intro c s t h
      simp [exec_zero] at h
  | succ k ih =>
      intro c s t h
      cases c with
      | skip =>
          rw [exec_skip] at h
          simp at h
          subst h
          exact BigStep.skip _
      | assign name value =>
          rw [exec_assign] at h
          simp at h
          subst h
          exact BigStep.assign _ _ _
      | seq first second =>
          cases hfirst : exec k first s with
          | none =>
              rw [exec_seq_none hfirst] at h
              simp at h
          | some m =>
              rw [exec_seq_some hfirst] at h
              exact BigStep.seq (ih hfirst) (ih h)
      | ite guard thenBranch elseBranch =>
          cases hguard : guard.eval s with
          | true =>
              rw [exec_ite_true hguard] at h
              exact BigStep.iteTrue hguard (ih h)
          | false =>
              rw [exec_ite_false hguard] at h
              exact BigStep.iteFalse hguard (ih h)
      | «while» guard body =>
          cases hguard : guard.eval s with
          | true =>
              cases hbody : exec k body s with
              | none =>
                  rw [exec_while_true_none hguard hbody] at h
                  simp at h
              | some m =>
                  rw [exec_while_true_some hguard hbody] at h
                  exact BigStep.whileTrue hguard (ih hbody) (ih h)
          | false =>
              rw [exec_while_false hguard] at h
              simp at h
              subst h
              exact BigStep.whileFalse hguard

/-- Successful-result monotonicity: success at some fuel persists at
every larger fuel with the same final state. -/
theorem exec_mono {f₁ f₂ : Nat} {c : Cmd} {s t : State}
    (hle : f₁ ≤ f₂) (h : exec f₁ c s = some t) :
    exec f₂ c s = some t := by
  revert f₂ c s t
  induction f₁ with
  | zero =>
      intro f₂ c s t hle h
      simp [exec_zero] at h
  | succ k ih =>
      intro f₂ c s t hle h
      cases f₂ with
      | zero =>
          simp at hle
      | succ j =>
          have hkj : k ≤ j := Nat.le_of_succ_le_succ hle
          cases c with
          | skip =>
              rw [exec_skip] at h ⊢
              exact h
          | assign name value =>
              rw [exec_assign] at h ⊢
              exact h
          | seq first second =>
              cases hfirst : exec k first s with
              | none =>
                  rw [exec_seq_none hfirst] at h
                  simp at h
              | some m =>
                  rw [exec_seq_some hfirst] at h
                  have hfirst' : exec j first s = some m :=
                    ih hkj hfirst
                  rw [exec_seq_some hfirst']
                  exact ih hkj h
          | ite guard thenBranch elseBranch =>
              cases hguard : guard.eval s with
              | true =>
                  rw [exec_ite_true hguard] at h ⊢
                  exact ih hkj h
              | false =>
                  rw [exec_ite_false hguard] at h ⊢
                  exact ih hkj h
          | «while» guard body =>
              cases hguard : guard.eval s with
              | true =>
                  cases hbody : exec k body s with
                  | none =>
                      rw [exec_while_true_none hguard hbody] at h
                      simp at h
                  | some m =>
                      rw [exec_while_true_some hguard hbody] at h
                      have hbody' : exec j body s = some m :=
                        ih hkj hbody
                      rw [exec_while_true_some hguard hbody']
                      exact ih hkj h
              | false =>
                  rw [exec_while_false hguard] at h ⊢
                  exact h

/-- Completeness: every canonical `BigStep` derivation succeeds at
some fuel, via maxima of premise fuels plus one. -/
theorem exists_fuel_of_bigStep {c : Cmd} {s t : State}
    (h : BigStep c s t) : ∃ fuel, exec fuel c s = some t := by
  induction h with
  | skip s =>
      exact ⟨0 + 1, exec_skip⟩
  | assign s name value =>
      exact ⟨0 + 1, exec_assign⟩
  | seq _ _ ihfirst ihsecond =>
      obtain ⟨f₁, hf₁⟩ := ihfirst
      obtain ⟨f₂, hf₂⟩ := ihsecond
      refine ⟨max f₁ f₂ + 1, ?_⟩
      have e₁ := exec_mono (Nat.le_max_left f₁ f₂) hf₁
      have e₂ := exec_mono (Nat.le_max_right f₁ f₂) hf₂
      rw [exec_seq_some e₁]
      exact e₂
  | iteTrue hguard _ ih =>
      obtain ⟨f, hf⟩ := ih
      refine ⟨f + 1, ?_⟩
      rw [exec_ite_true hguard]
      exact hf
  | iteFalse hguard _ ih =>
      obtain ⟨f, hf⟩ := ih
      refine ⟨f + 1, ?_⟩
      rw [exec_ite_false hguard]
      exact hf
  | whileFalse hguard =>
      exact ⟨0 + 1, exec_while_false hguard⟩
  | whileTrue hguard _ _ ihbody ihloop =>
      obtain ⟨fb, hfb⟩ := ihbody
      obtain ⟨fl, hfl⟩ := ihloop
      refine ⟨max fb fl + 1, ?_⟩
      have e₁ := exec_mono (Nat.le_max_left fb fl) hfb
      have e₂ := exec_mono (Nat.le_max_right fb fl) hfl
      rw [exec_while_true_some hguard e₁]
      exact e₂

end Cslib.IMP

#print axioms Cslib.IMP.exec
#print axioms Cslib.IMP.exec_zero
#print axioms Cslib.IMP.exec_skip
#print axioms Cslib.IMP.exec_assign
#print axioms Cslib.IMP.exec_seq_none
#print axioms Cslib.IMP.exec_seq_some
#print axioms Cslib.IMP.exec_ite_true
#print axioms Cslib.IMP.exec_ite_false
#print axioms Cslib.IMP.exec_while_false
#print axioms Cslib.IMP.exec_while_true_none
#print axioms Cslib.IMP.exec_while_true_some
#print axioms Cslib.IMP.exec_sound
#print axioms Cslib.IMP.exec_mono
#print axioms Cslib.IMP.exists_fuel_of_bigStep
