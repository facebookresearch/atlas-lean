/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Dynamics.RokhlinLemma
import Mathlib.Dynamics.Ergodic.AddCircle

/-! # Tests for Rokhlin towers -/

namespace MathlibExtTest.Dynamics.RokhlinLemma

open Function MeasureTheory Set
open MathlibExt.Dynamics.RokhlinLemmaWanted.Dynamics

-- Height zero has no floors. At height one, the union is exactly the base.
example {α : Type*} (T : α → α) (B : Set α) : towerUnion T B 0 = ∅ := by
  simp [towerUnion]

example {α : Type*} (T : α → α) (B : Set α) : towerUnion T B 1 = B := by
  simp [towerUnion, towerFloor]

-- The forward floor is a singleton even though the preimage of this base is empty.
example : towerFloor (fun _ : Bool ↦ true) {false} 1 = {true} := by
  simp [towerFloor]

-- Every point of period k for circle doubling is killed by 2^k - 1.
-- These torsion sets are finite, so their countable union is Haar-null.
private theorem doubling_aperiodic :
    IsAperiodic (fun x : UnitAddCircle ↦ (2 : ℕ) • x) volume := by
  let F (j : ℕ) := {x : UnitAddCircle | (2 ^ (j + 1) - 1 : ℕ) • x = 0}
  have hF j : (F j).Finite := AddCircle.finite_torsion 1 (by
    have := one_lt_pow₀ (by decide : 1 < (2 : ℕ)) (Nat.succ_ne_zero j)
    omega)
  apply Set.Countable.measure_zero
  apply (Set.countable_iUnion fun j ↦ (hF j).countable).mono
  intro x hx
  obtain ⟨k, hk, hfix⟩ := mem_periodicPts.mp hx
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  refine mem_iUnion.mpr ⟨j, ?_⟩
  have hpow : (2 ^ (j + 1) : ℕ) • x = x := by
    simpa only [IsPeriodicPt, IsFixedPt, smul_iterate_apply] using hfix
  change (2 ^ (j + 1) - 1 : ℕ) • x = 0
  rw [sub_nsmul _ (Nat.succ_le_of_lt (by positivity)), one_nsmul, hpow, add_neg_cancel]

example (n : ℕ) (hn : 1 ≤ n) {ε : ENNReal} (hε : 0 < ε) :
    ∃ B : Set UnitAddCircle, IsRokhlinTower (fun x ↦ (2 : ℕ) • x) B n ∧
      1 - ε ≤ volume (towerUnion (fun x ↦ (2 : ℕ) • x) B n) := by
  let : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩
  have hT := AddCircle.ergodic_nsmul (T := (1 : ℝ)) (by decide : 1 < (2 : ℕ))
  exact rokhlin_lemma volume _ hT.toMeasurePreserving doubling_aperiodic n hn hε

end MathlibExtTest.Dynamics.RokhlinLemma
