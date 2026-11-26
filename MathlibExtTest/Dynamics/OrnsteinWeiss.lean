/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Dynamics.OrnsteinWeiss
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.NumberTheory.Real.Irrational

/-! # Tests for the multidimensional Rokhlin lemma -/

namespace MathlibExtTest.Dynamics.OrnsteinWeiss

open MeasureTheory Set
open MathlibExt.Dynamics.OrnsteinWeissWanted.Dynamics

-- The square contains four levels and excludes the upper endpoint in either coordinate.
example : (boxShape 2 2).card = 4 := by
  simp [boxShape, Fintype.card_piFinset, Int.card_Ico]

example : ![0, 2] ∉ boxShape 2 2 := by
  intro h
  have := Finset.mem_Ico.mp (Fintype.mem_piFinset.mp h 1)
  norm_num at this

private abbrev Torus := UnitAddCircle × UnitAddCircle

private noncomputable def rotate (v : Fin 2 → ℤ) (x : Torus) : Torus :=
  let a := (Real.sqrt 2 : UnitAddCircle)
  (v 0 • a, v 1 • a) + x

-- Translation by sqrt(2) on each circle has no fixed points for a nonzero lattice vector.
private theorem rotate_free (μ : Measure Torus) : IsFreeAction μ rotate := by
  have horder : addOrderOf (Real.sqrt 2 : UnitAddCircle) = 0 := by
    apply addOrderOf_eq_zero_iff.mpr
    apply AddCircle.not_isOfFinAddOrder_iff_forall_rat_ne_div.mpr
    intro q hq
    exact irrational_sqrt_two ⟨q, by simpa using hq⟩
  intro v hv
  suffices {x | rotate v x = x} = ∅ by simp [this]
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have h : (v 0 • (Real.sqrt 2 : UnitAddCircle), v 1 • (Real.sqrt 2 : UnitAddCircle)) = 0 :=
    add_right_cancel (b := x) (by simpa only [mem_ofPred_eq, rotate, zero_add] using hx)
  apply hv
  funext i
  fin_cases i
  · simpa [← addOrderOf_dvd_iff_zsmul_eq_zero, horder] using congrArg Prod.fst h
  · simpa [← addOrderOf_dvd_iff_zsmul_eq_zero, horder] using congrArg Prod.snd h

example (N : ℕ) (hN : 1 ≤ N) {ε : ENNReal} (hε : 0 < ε) :
    ∃ B : Set Torus, MeasurableSet B ∧
      (boxShape 2 N : Set (Fin 2 → ℤ)).PairwiseDisjoint (fun v ↦ rotate v '' B) ∧
      1 - ε ≤ (volume.prod volume) (⋃ v ∈ boxShape 2 N, rotate v '' B) := by
  let : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩
  apply ornstein_weiss_rokhlin (by decide) _ rotate _ _ _ (rotate_free _) N hN hε
  · intro x
    simp [rotate]
  · intro v
    exact measurePreserving_add_left _ _
  · intro u v x
    ext <;> simp [rotate, add_zsmul, add_assoc]

end MathlibExtTest.Dynamics.OrnsteinWeiss
