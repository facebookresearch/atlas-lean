/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.TailCondLawConstant

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.TailCondLawConstant`

* non-vacuity of `atl_TailSelMP`: `atl_tailSelMP_of_stop_le` at `s = n`, using `stopVal_le`,
  for the FK mass on `K₂` at `p = 1/2`, `q = 2`;
* `atl_tailCondLaw_const_switch` for the same mass and the constant observable `0`, whose
  stopping value is `0` (head-determined);
* `atl_tailCondLaw_of_residues` stated by name.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.TailCondLawConstant

open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.AdaptDisintegration
open _root_.StatMech.OSSS.MonotonicFK _root_.StatMech.OSSS.AdaptMConditional

-- The tail selection is measure preserving once `s` is past every stopping value.
example {n : ℕ} (σ : Fin n ≃ Sym2 (Fin 2)) (f : ConfigSpace (Sym2 (Fin 2)) → ℝ) (t : ℕ)
    (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
    atl_TailSelMP (fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) σ f t n A :=
  atl_tailSelMP_of_stop_le σ t n A (fun _ => stopVal_le _ σ f _)

/-- A constant observable is determined at step `0`. -/
theorem stopVal_zero {n : ℕ} (σ : Fin n ≃ Sym2 (Fin 2)) (U : Fin n → ℝ) :
    stopVal (fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) σ (fun _ => 0) U = 0 := by
  simp [stopVal, stopValC, detAtC]

-- The tail conditional law for the constant observable, via the constant switch.
example {n : ℕ} (σ : Fin n ≃ Sym2 (Fin 2)) :
    acp_TailCondLaw (fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) σ (fun _ => 0) :=
  atl_tailCondLaw_const_switch (fkMass_pos ⊤ (by norm_num) (by norm_num) (by norm_num))
    (fkMass_sum_eq_one ⊤ (by norm_num) (by norm_num) (by norm_num))
    (fkMass_isMonotonic ⊤ (by norm_num) (by norm_num) (by norm_num)) σ monotone_const
    (fun _ => by norm_num) (fun _ _ => 0) (fun _ _ _ => stopVal_zero σ _)

-- The residue assembly exists with the expected name.
example := @atl_tailCondLaw_of_residues

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.TailCondLawConstant
