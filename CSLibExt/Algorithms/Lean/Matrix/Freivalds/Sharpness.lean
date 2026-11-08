/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Matrix.Freivalds.Basic
public import CSLibExt.Algorithms.Lean.Matrix.Freivalds.Amplification
public import Batteries.Data.Vector.Lemmas
import Mathlib.Tactic

/-!
# A sharp binary Freivalds example

For the one-by-one inputs `A = B = [1]` and `C = [0]`, the actual trial
accepts precisely the zero seed. This supplies the boundary example for the
one-half error bound in MIT 6.046J Spring 2015 Lecture 6, printed page 2.
All matrices and arithmetic here are over `ZMod 2` by intentional GF(2) specialization (see
`Freivalds.Basic`); the lecture itself only takes the seed vector binary over a general
coefficient domain.

Retained Lean was authored by Codex at Adam Kiezun's explicit selection.
-/

set_option autoImplicit false

open scoped ENNReal

@[expose] public section

namespace Cslib.Algorithms.Lean.Matrix

/-- The sharpness inputs really have an incorrect matrix product. -/
theorem freivalds_one_wrong :
    freivaldsMatrix
        (_root_.Vector.replicate 1 (_root_.Vector.replicate 1 (1 : ZMod 2))) *
      freivaldsMatrix
        (_root_.Vector.replicate 1 (_root_.Vector.replicate 1 (1 : ZMod 2))) ≠
      freivaldsMatrix
        (_root_.Vector.replicate 1 (_root_.Vector.replicate 1 (0 : ZMod 2))) := by
  intro equal
  have first := congrFun (congrFun equal 0) 0
  simp [freivaldsMatrix, _root_.Matrix.mul_apply, _root_.Vector.get_replicate] at first

/-- The actual one-by-one incorrect-product trial accepts exactly the zero bit. -/
theorem freivaldsTrial_one_accept_iff (r : Fin 1 → ZMod 2) :
    (freivaldsTrial
      (_root_.Vector.replicate 1 (_root_.Vector.replicate 1 (1 : ZMod 2)))
      (_root_.Vector.replicate 1 (_root_.Vector.replicate 1 (1 : ZMod 2)))
      (_root_.Vector.replicate 1 (_root_.Vector.replicate 1 (0 : ZMod 2))) r).ret = true ↔
        r 0 = 0 := by
  rw [freivaldsTrial_accept_iff]
  constructor
  · intro equal
    have first := congrFun equal 0
    simpa [freivaldsMatrix, _root_.Matrix.mulVec_apply_eq_sum,
      _root_.Vector.get_replicate] using first
  · intro zero
    funext i
    have index : i = 0 := Subsingleton.elim i 0
    subst i
    simp [freivaldsMatrix, _root_.Matrix.mulVec_apply_eq_sum, zero]

/-- Exactly one complete one-dimensional seed is accepted by the wrong-product trial. -/
theorem freivaldsTrial_one_acceptanceCard :
    Fintype.card {r : Fin 1 → ZMod 2 //
      (freivaldsTrial
        (_root_.Vector.replicate 1 (_root_.Vector.replicate 1 (1 : ZMod 2)))
        (_root_.Vector.replicate 1 (_root_.Vector.replicate 1 (1 : ZMod 2)))
        (_root_.Vector.replicate 1 (_root_.Vector.replicate 1 (0 : ZMod 2))) r).ret = true} =
      1 := by
  classical
  let _ : Unique {r : Fin 1 → ZMod 2 //
      (freivaldsTrial
        (_root_.Vector.replicate 1 (_root_.Vector.replicate 1 (1 : ZMod 2)))
        (_root_.Vector.replicate 1 (_root_.Vector.replicate 1 (1 : ZMod 2)))
        (_root_.Vector.replicate 1 (_root_.Vector.replicate 1 (0 : ZMod 2))) r).ret = true} := {
    default := ⟨fun _ => 0, (freivaldsTrial_one_accept_iff (fun _ => 0)).mpr rfl⟩
    uniq := by
      intro r
      apply Subtype.ext
      funext i
      have index : i = 0 := Subsingleton.elim i 0
      subst i
      exact (freivaldsTrial_one_accept_iff r.val).mp r.property
  }
  exact Fintype.card_unique

/-- The actual wrong-product trial attains the one-half error bound. -/
theorem freivaldsTrialLaw_one_sharp :
    freivaldsTrialLaw
      (_root_.Vector.replicate 1 (_root_.Vector.replicate 1 (1 : ZMod 2)))
      (_root_.Vector.replicate 1 (_root_.Vector.replicate 1 (1 : ZMod 2)))
      (_root_.Vector.replicate 1 (_root_.Vector.replicate 1 (0 : ZMod 2))) true =
        (1 : ℝ≥0∞) / 2 := by
  rw [freivaldsTrialLaw_acceptance, freivaldsTrial_one_acceptanceCard]
  simp

/-- The same incorrect inputs attain the repeated error bound for every trial count. -/
theorem freivaldsRepeatLaw_one_sharp (k : Nat) :
    freivaldsRepeatLaw k
      (_root_.Vector.replicate 1 (_root_.Vector.replicate 1 (1 : ZMod 2)))
      (_root_.Vector.replicate 1 (_root_.Vector.replicate 1 (1 : ZMod 2)))
      (_root_.Vector.replicate 1 (_root_.Vector.replicate 1 (0 : ZMod 2))) true =
        ((2 : ℝ≥0∞) ^ k)⁻¹ := by
  rw [freivaldsRepeatLaw_acceptance_power, freivaldsTrialLaw_one_sharp]
  simp [div_eq_mul_inv, ENNReal.inv_pow]

end Cslib.Algorithms.Lean.Matrix
