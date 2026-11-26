/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveCodingLaw

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveCodingLaw`

* non-vacuity of `PredictableOrder`: every constant order is predictable;
* `predictable_adaptive_fibres_full_measure` for the random-cluster mass on the complete graph on
  `Fin 2` at `p = 1/2`, `q = 2`, with a constant order;
* `integral_g_adaptiveCode` for the same mass and the open-edge observable of `s(0, 1)`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveCodingLaw

open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.AdaptiveCodingLaw
open _root_.StatMech.OSSS.MonotonicFK MeasureTheory

/-- The random-cluster mass on `K₂` at `p = 1/2`, `q = 2`. -/
local notation "μ₂" => fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2

/-- Positivity of `μ₂`. -/
theorem mu2_pos (ω : ConfigSpace (Sym2 (Fin 2))) : 0 < μ₂ ω :=
  fkMass_pos ⊤ (by norm_num) (by norm_num) (by norm_num) ω

/-- `μ₂` is a probability mass. -/
theorem mu2_sum : ∑ ω, μ₂ ω = 1 :=
  fkMass_sum_eq_one ⊤ (by norm_num) (by norm_num) (by norm_num)

/-- Non-vacuity: a constant revealment order is predictable. -/
theorem predictableOrder_const {E : Type*} [DecidableEq E] {n : ℕ} (τ : Fin n ≃ E) :
    PredictableOrder (fun _ : ConfigSpace E => τ) :=
  fun _ _ _ _ => rfl

-- The adaptive fibres of the FK mass on `K₂` cover almost every label.
example {n : ℕ} (τ : Fin n ≃ Sym2 (Fin 2)) :
    ((GrandCoupling.Vcube n) (⋃ x, adaptiveFibre μ₂ (fun _ => τ) x)).toReal = 1 :=
  predictable_adaptive_fibres_full_measure μ₂ mu2_pos
    mu2_sum _ (predictableOrder_const τ)

-- Integrals against the adaptive code are expectations under the FK mass on `K₂`.
example {n : ℕ} (τ : Fin n ≃ Sym2 (Fin 2)) :
    ∫ u, (if adaptiveCode μ₂ (fun _ => τ) u s(0, 1) then (1 : ℝ) else 0)
        ∂(GrandCoupling.Vcube n) =
      ∑ x, (if x s(0, 1) then (1 : ℝ) else 0) * μ₂ x :=
  integral_g_adaptiveCode μ₂ mu2_pos
    mu2_sum _ (predictableOrder_const τ)
    (fun x => if x s(0, 1) then (1 : ℝ) else 0)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveCodingLaw
