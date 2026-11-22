/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.IMP.HoareTotal
public import Mathlib.Data.Nat.GCD.Basic

@[expose] public section

namespace Cslib.IMP.HoareGcd

/-- Swap the values of variables `0` (`x`) and `1` (`y`) via variable `2`
(`tmp`): `tmp := x; x := y; y := tmp`. -/
def swap : Cmd :=
  .seq (.assign 2 (.var 0))
    (.seq (.assign 0 (.var 1)) (.assign 1 (.var 2)))

/-- Partial correctness of `swap`, proved with the assignment and sequence
rules, working backwards through `Assertion.subst`. -/
theorem swap_correct (a b : Nat) :
    Valid (fun s => s 0 = a ∧ s 1 = b) swap (fun s => s 0 = b ∧ s 1 = a) := by
  refine Valid.consequence (command := swap) ?_
    (Valid.seq (Valid.assign _ _ _)
      (Valid.seq (Valid.assign _ _ _) (Valid.assign _ _ _)))
    (Assertion.entails_refl _)
  intro s hs
  simp only [Assertion.subst, AExp.eval_var]
  simp [Function.update, hs.1, hs.2]

/-- Loop guard of the subtraction gcd: `x ≠ y`. -/
def gcdGuard : BExp :=
  .not (.eq (.var 0) (.var 1))

/-- Loop body of the subtraction gcd: `if x ≤ y then y := y - x else x := x - y`. -/
def gcdBody : Cmd :=
  .ite (.le (.var 0) (.var 1))
    (.assign 1 (.sub (.var 1) (.var 0)))
    (.assign 0 (.sub (.var 0) (.var 1)))

/-- Euclid's gcd by repeated subtraction on variables `0` (`x`) and `1` (`y`). -/
def gcdCmd : Cmd :=
  .while gcdGuard gcdBody

/-- Loop invariant: both values stay positive and their gcd never changes. -/
abbrev gcdInv (d : Nat) : Assertion :=
  fun s => 0 < s 0 ∧ 0 < s 1 ∧ Nat.gcd (s 0) (s 1) = d

/-- One guarded body execution restores the invariant and strictly decreases
the variant `x + y`. The guard gives `x ≠ y`, so the truncated subtraction in
the taken branch is a genuine, positive decrease. -/
theorem gcdBody_step (d : Nat) :
    ∀ s, gcdInv d s → gcdGuard.eval s = true →
      ∃ s', BigStep gcdBody s s' ∧ gcdInv d s' ∧ s' 0 + s' 1 < s 0 + s 1 := by
  intro s hs hguard
  obtain ⟨hx, hy, hg⟩ := hs
  have hne : s 0 ≠ s 1 := by
    have hfalse : (BExp.eq (.var 0) (.var 1)).eval s = false :=
      BExp.eval_not_eq_true.mp hguard
    intro heq
    have htrue : (BExp.eq (.var 0) (.var 1)).eval s = true :=
      BExp.eval_eq_eq_true.mpr heq
    rw [hfalse] at htrue
    exact Bool.false_ne_true htrue
  by_cases hle : s 0 ≤ s 1
  · have hlt : s 0 < s 1 := lt_of_le_of_ne hle hne
    have hguardLe : (BExp.le (.var 0) (.var 1)).eval s = true :=
      BExp.eval_le_eq_true.mpr hle
    have h0 : (Function.update s 1 (s 1 - s 0)) 0 = s 0 := by
      simp [Function.update]
    have h1 : (Function.update s 1 (s 1 - s 0)) 1 = s 1 - s 0 := by
      simp [Function.update]
    refine ⟨Function.update s 1 (s 1 - s 0), ?_, ⟨?_, ?_, ?_⟩, ?_⟩
    · show BigStep (.ite (.le (.var 0) (.var 1))
          (.assign 1 (.sub (.var 1) (.var 0)))
          (.assign 0 (.sub (.var 0) (.var 1)))) s _
      exact .iteTrue hguardLe (.assign s 1 _)
    · rw [h0]; exact hx
    · rw [h1]; omega
    · rw [h0, h1, Nat.gcd_sub_self_right hle]; exact hg
    · rw [h0, h1]; omega
  · have hlt : s 1 < s 0 := by omega
    have hle' : s 1 ≤ s 0 := by omega
    have hguardLe : (BExp.le (.var 0) (.var 1)).eval s = false := by
      cases h : (BExp.le (.var 0) (.var 1)).eval s with
      | false => rfl
      | true => exact absurd (BExp.eval_le_eq_true.mp h) hle
    have h0 : (Function.update s 0 (s 0 - s 1)) 0 = s 0 - s 1 := by
      simp [Function.update]
    have h1 : (Function.update s 0 (s 0 - s 1)) 1 = s 1 := by
      simp [Function.update]
    refine ⟨Function.update s 0 (s 0 - s 1), ?_, ⟨?_, ?_, ?_⟩, ?_⟩
    · show BigStep (.ite (.le (.var 0) (.var 1))
          (.assign 1 (.sub (.var 1) (.var 0)))
          (.assign 0 (.sub (.var 0) (.var 1)))) s _
      exact .iteFalse hguardLe (.assign s 0 _)
    · rw [h0]; omega
    · rw [h1]; exact hy
    · rw [h0, h1, Nat.gcd_sub_self_left hle']; exact hg
    · rw [h0, h1]; omega

/-- Total correctness of Euclid's gcd by repeated subtraction, via the
variant rule with invariant `gcdInv d` and variant `x + y`. -/
theorem gcd_total (d : Nat) :
    TValid (fun s => 0 < s 0 ∧ 0 < s 1 ∧ Nat.gcd (s 0) (s 1) = d) gcdCmd
      (fun s => s 0 = d ∧ s 1 = d) := by
  refine TValid.consequence (pre' := gcdInv d)
    (post' := fun s => gcdInv d s ∧ gcdGuard.eval s = false)
    (command := gcdCmd) ?_ ?_ ?_
  · intro s hs
    exact hs
  · show TValid (gcdInv d) (.while gcdGuard gcdBody) _
    exact TValid.whileVariant (variant := fun s => s 0 + s 1) (gcdBody_step d)
  · intro s hs
    obtain ⟨⟨_hx, _hy, hg⟩, hguard⟩ := hs
    have heq : s 0 = s 1 := by
      have htrue : (BExp.eq (.var 0) (.var 1)).eval s = true := by
        cases h : (BExp.eq (.var 0) (.var 1)).eval s with
        | true => rfl
        | false =>
            have hnot : gcdGuard.eval s = true :=
              BExp.eval_not_eq_true.mpr h
            rw [hnot] at hguard
            simp at hguard
      exact BExp.eval_eq_eq_true.mp htrue
    have hsd : s 0 = d := by
      have h := hg
      rw [← heq, Nat.gcd_self] at h
      exact h
    refine ⟨hsd, ?_⟩
    rw [← heq]
    exact hsd

/-- Initial state with `x = 12` and `y = 18`. -/
def gcdInit1218 : State :=
  Function.update (Function.update (fun _ => 0) 0 12) 1 18

/-- Concrete corollary: `gcdCmd` computes `gcd 12 18 = 6` and terminates. -/
theorem gcd_12_18 :
    ∃ final, Terminates gcdCmd gcdInit1218 final ∧ final 0 = 6 ∧ final 1 = 6 := by
  have h0 : gcdInit1218 0 = 12 := by simp [gcdInit1218, Function.update]
  have h1 : gcdInit1218 1 = 18 := by simp [gcdInit1218, Function.update]
  have hpre : 0 < gcdInit1218 0 ∧ 0 < gcdInit1218 1 ∧
      Nat.gcd (gcdInit1218 0) (gcdInit1218 1) = 6 := by
    rw [h0, h1]
    exact ⟨by omega, by omega, by decide⟩
  obtain ⟨final, hterm, hpost⟩ := TValid.terminates (gcd_total 6) hpre
  exact ⟨final, hterm, hpost⟩

#print axioms swap_correct
#print axioms gcd_total
#print axioms gcd_12_18

end Cslib.IMP.HoareGcd
