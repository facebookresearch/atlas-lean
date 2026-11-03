/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.TailSelMP

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.TailSelMP`

For the FK mass on the complete graph `K₂` at `p = 1/2`, `q = 2`, and the constant observable
`0` (stopping value `0` everywhere):

* `tsm_switchPiece_const_eq`: the switch piece at `0` is everything;
* non-vacuity of `tsm_TailSelMP_restrictedSum` via `tsm_restrictedSum_of_const`;
* `tsm_tailSelMP_of_restrictedSum`: the stopped tail selection is measure preserving.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.TailSelMP

open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.AdaptDisintegration
open _root_.StatMech.OSSS.MonotonicFK _root_.StatMech.OSSS.AdaptMConditional

/-- A constant observable is determined at step `0`. -/
theorem stopVal_zero {n : ℕ} (σ : Fin n ≃ Sym2 (Fin 2)) (U : Fin n → ℝ) :
    stopVal (fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) σ (fun _ => 0) U = 0 := by
  simp [stopVal, stopValC, detAtC]

-- The switch piece at the constant stopping value is everything.
example {n : ℕ} (σ : Fin n ≃ Sym2 (Fin 2)) (t : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
    tsm_switchPiece (fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) σ (fun _ => 0) t A 0
      = Set.univ :=
  tsm_switchPiece_const_eq _ σ t A 0 (fun _ => stopVal_zero σ _)

-- The restricted-sum identity holds for a head-determined stopping value.
example {n : ℕ} (σ : Fin n ≃ Sym2 (Fin 2)) (A : {i : Fin n // (i : ℕ) < 0} → ℝ) :
    tsm_TailSelMP_restrictedSum (fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) σ (fun _ => 0)
      0 1 A :=
  tsm_restrictedSum_of_const _ σ 0 1 (by norm_num) A 0 (fun _ => stopVal_zero σ _)

-- Hence the stopped tail selection is measure preserving.
example {n : ℕ} (σ : Fin n ≃ Sym2 (Fin 2)) (A : {i : Fin n // (i : ℕ) < 0} → ℝ) :
    atl_TailSelMP (fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) σ (fun _ => 0) 0 1 A :=
  tsm_tailSelMP_of_restrictedSum _ σ _ 0 1 A
    (tsm_restrictedSum_of_const _ σ 0 1 (by norm_num) A 0 (fun _ => stopVal_zero σ _))

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.TailSelMP
