/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.IMP.Hoare

/-!
# Hoare logic: worked examples

Concrete verified programs using the Hoare rules in
`CSLibExt/Languages/IMP/Hoare.lean` (`Valid.skip`, `Valid.assign`,
`Valid.seq`, `Valid.ite`, `Valid.whileLoop`, `Valid.consequence`).

Variables are `x = 0`, `y = 1`, `t = 2`, `s = 0`, `i = 1`, `m = 2`
in the respective programs. The three examples exercise the three
non-trivial rules: assignment sequencing (swap), the conditional (max),
and the invariant rule (countdown loop).
-/

@[expose] public section

namespace Cslib
namespace IMP
namespace Examples

/-- Swap `x` and `y` through the temporary `t`. -/
def swapProg : Cmd :=
  .seq (.assign 2 (.var 0))
    (.seq (.assign 0 (.var 1)) (.assign 1 (.var 2)))

/-- Swapping exchanges the values of `x` and `y`. -/
theorem swap_valid (a b : Nat) :
    Valid (fun s => s 0 = a ∧ s 1 = b) swapProg
      (fun s => s 0 = b ∧ s 1 = a) := by
  have h1 : Valid (fun s => s 0 = a ∧ s 1 = b) (.assign 2 (.var 0))
      (fun s => s 0 = a ∧ s 1 = b ∧ s 2 = a) := by
    have hpre : Assertion.Entails (fun s => s 0 = a ∧ s 1 = b)
        (Assertion.subst (fun s => s 0 = a ∧ s 1 = b ∧ s 2 = s 0) 2 (.var 0)) := by
      intro s h
      simp [Assertion.subst, Function.update] at h ⊢
      omega
    have hpost : Assertion.Entails (fun s => s 0 = a ∧ s 1 = b ∧ s 2 = s 0)
        (fun s => s 0 = a ∧ s 1 = b ∧ s 2 = a) := by
      intro s h
      omega
    exact Valid.consequence hpre
      (Valid.assign (fun s => s 0 = a ∧ s 1 = b ∧ s 2 = s 0) 2 (.var 0)) hpost
  have h2 : Valid (fun s => s 0 = a ∧ s 1 = b ∧ s 2 = a) (.assign 0 (.var 1))
      (fun s => s 0 = b ∧ s 1 = b ∧ s 2 = a) := by
    have hpre : Assertion.Entails (fun s => s 0 = a ∧ s 1 = b ∧ s 2 = a)
        (Assertion.subst (fun s => s 0 = b ∧ s 1 = b ∧ s 2 = a) 0 (.var 1)) := by
      intro s h
      simp [Assertion.subst, Function.update] at h ⊢
      omega
    have hpost : Assertion.Entails (fun s => s 0 = b ∧ s 1 = b ∧ s 2 = a)
        (fun s => s 0 = b ∧ s 1 = b ∧ s 2 = a) := by
      intro s h
      exact h
    exact Valid.consequence hpre
      (Valid.assign (fun s => s 0 = b ∧ s 1 = b ∧ s 2 = a) 0 (.var 1)) hpost
  have h3 : Valid (fun s => s 0 = b ∧ s 1 = b ∧ s 2 = a) (.assign 1 (.var 2))
      (fun s => s 0 = b ∧ s 1 = a) := by
    have hpre : Assertion.Entails (fun s => s 0 = b ∧ s 1 = b ∧ s 2 = a)
        (Assertion.subst (fun s => s 0 = b ∧ s 1 = a) 1 (.var 2)) := by
      intro s h
      simp [Assertion.subst, Function.update] at h ⊢
      omega
    have hpost : Assertion.Entails (fun s => s 0 = b ∧ s 1 = a)
        (fun s => s 0 = b ∧ s 1 = a) := by
      intro s h
      exact h
    exact Valid.consequence hpre
      (Valid.assign (fun s => s 0 = b ∧ s 1 = a) 1 (.var 2)) hpost
  exact Valid.seq h1 (Valid.seq h2 h3)

/-- `m := max x y` by a conditional. -/
def maxProg : Cmd :=
  .ite (BExp.le (.var 0) (.var 1)) (.assign 2 (.var 1)) (.assign 2 (.var 0))

/-- The conditional computes the maximum of `x` and `y` into `m`. -/
theorem max_valid (a b : Nat) :
    Valid (fun s => s 0 = a ∧ s 1 = b) maxProg
      (fun s => s 2 = Nat.max a b) := by
  have hthen : Valid
      (fun s => (s 0 = a ∧ s 1 = b) ∧ (BExp.le (.var 0) (.var 1)).eval s = true)
      (.assign 2 (.var 1)) (fun s => s 2 = Nat.max a b) := by
    have hpre : Assertion.Entails (fun s => (s 0 = a ∧ s 1 = b) ∧
        (BExp.le (.var 0) (.var 1)).eval s = true)
        (Assertion.subst (fun s => s 2 = Nat.max a b) 2 (.var 1)) := by
      intro s h
      have hle : s 0 ≤ s 1 := BExp.eval_le_eq_true.mp h.2
      have hmax : Nat.max a b = b := max_eq_right (by omega)
      simp [Assertion.subst, Function.update] at h ⊢
      rw [hmax]
      omega
    exact Valid.consequence hpre
      (Valid.assign (fun s => s 2 = Nat.max a b) 2 (.var 1))
      (by intro s h; exact h)
  have helse : Valid
      (fun s => (s 0 = a ∧ s 1 = b) ∧ (BExp.le (.var 0) (.var 1)).eval s = false)
      (.assign 2 (.var 0)) (fun s => s 2 = Nat.max a b) := by
    have hpre : Assertion.Entails (fun s => (s 0 = a ∧ s 1 = b) ∧
        (BExp.le (.var 0) (.var 1)).eval s = false)
        (Assertion.subst (fun s => s 2 = Nat.max a b) 2 (.var 0)) := by
      intro s h
      have hnle : ¬ s 0 ≤ s 1 := by
        intro hle
        have htrue : (BExp.le (.var 0) (.var 1)).eval s = true :=
          BExp.eval_le_eq_true.mpr hle
        rw [h.2] at htrue
        exact Bool.false_ne_true htrue
      have hmax : Nat.max a b = a := max_eq_left (by omega)
      simp [Assertion.subst, Function.update] at h ⊢
      rw [hmax]
      omega
    exact Valid.consequence hpre
      (Valid.assign (fun s => s 2 = Nat.max a b) 2 (.var 0))
      (by intro s h; exact h)
  exact Valid.ite hthen helse

/-- Countdown: `s := s + 1; i := i - 1` while `0 < i`. -/
def countdownProg : Cmd :=
  .while (BExp.le (.const 1) (.var 1))
    (.seq (.assign 0 (.add (.var 0) (.const 1)))
      (.assign 1 (.sub (.var 1) (.const 1))))

/-- The countdown loop transfers `i` into `s`: starting from `s = a`,
`i = b`, it ends with `s = a + b` (and `i = 0`). -/
theorem countdown_valid (a b : Nat) :
    Valid (fun s => s 0 = a ∧ s 1 = b) countdownProg
      (fun s => s 0 = a + b ∧ s 1 = 0) := by
  have hbody : Valid
      (fun s => s 0 + s 1 = a + b ∧ (BExp.le (.const 1) (.var 1)).eval s = true)
      (.seq (.assign 0 (.add (.var 0) (.const 1)))
        (.assign 1 (.sub (.var 1) (.const 1))))
      (fun s => s 0 + s 1 = a + b) := by
    have h1 : Valid
        (fun s => s 0 + s 1 = a + b ∧ (BExp.le (.const 1) (.var 1)).eval s = true)
        (.assign 0 (.add (.var 0) (.const 1)))
        (fun s => s 0 + s 1 = a + b + 1 ∧
          (BExp.le (.const 1) (.var 1)).eval s = true) := by
      have hpre : Assertion.Entails (fun s => s 0 + s 1 = a + b ∧
          (BExp.le (.const 1) (.var 1)).eval s = true)
          (Assertion.subst (fun s => s 0 + s 1 = a + b + 1 ∧
            (BExp.le (.const 1) (.var 1)).eval s = true) 0
            (.add (.var 0) (.const 1))) := by
        intro s h
        simp [Assertion.subst, Function.update] at h ⊢
        omega
      exact Valid.consequence hpre
        (Valid.assign (fun s => s 0 + s 1 = a + b + 1 ∧
          (BExp.le (.const 1) (.var 1)).eval s = true) 0
          (.add (.var 0) (.const 1)))
        (by intro s h; exact h)
    have h2 : Valid
        (fun s => s 0 + s 1 = a + b + 1 ∧
          (BExp.le (.const 1) (.var 1)).eval s = true)
        (.assign 1 (.sub (.var 1) (.const 1)))
        (fun s => s 0 + s 1 = a + b) := by
      have hpre : Assertion.Entails (fun s => s 0 + s 1 = a + b + 1 ∧
          (BExp.le (.const 1) (.var 1)).eval s = true)
          (Assertion.subst (fun s => s 0 + s 1 = a + b) 1 (.sub (.var 1) (.const 1))) := by
        intro s h
        simp [Assertion.subst, Function.update] at h ⊢
        omega
      exact Valid.consequence hpre
        (Valid.assign (fun s => s 0 + s 1 = a + b) 1
          (.sub (.var 1) (.const 1)))
        (by intro s h; exact h)
    exact Valid.seq h1 h2
  have hloop : Valid (fun s => s 0 + s 1 = a + b) countdownProg
      (fun s => s 0 + s 1 = a + b ∧
        (BExp.le (.const 1) (.var 1)).eval s = false) :=
    Valid.whileLoop hbody
  have hpre : Assertion.Entails (fun s => s 0 = a ∧ s 1 = b)
      (fun s => s 0 + s 1 = a + b) := by
    intro s h
    omega
  have hpost : Assertion.Entails (fun s => s 0 + s 1 = a + b ∧
      (BExp.le (.const 1) (.var 1)).eval s = false)
      (fun s => s 0 = a + b ∧ s 1 = 0) := by
    intro s h
    have hnle : ¬ (1 ≤ s 1) := by
      intro hle
      have htrue : (BExp.le (.const 1) (.var 1)).eval s = true :=
        BExp.eval_le_eq_true.mpr hle
      rw [h.2] at htrue
      exact Bool.false_ne_true htrue
    omega
  exact Valid.consequence hpre hloop hpost

end Examples
end IMP
end Cslib
