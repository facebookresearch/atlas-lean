/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.FactorOneComponent

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.FactorOneComponent`

* `ofh_factor_one_component` with the bounded measurable test function `G = 1`, for an
  arbitrary weight, order, observable and step.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.FactorOneComponent

open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.Monotonic
open _root_.StatMech.OSSS.Coding _root_.StatMech.OSSS.GrandCoupling
open _root_.StatMech.OSSS.AdaptMConditional _root_.StatMech.OSSS.AdaptDisintegration
open _root_.StatMech.OSSS.AdaptiveTau _root_.StatMech.Probability MeasureTheory

-- One-coordinate factorization against the constant test function `1`.
example {E : Type*} [Fintype E] [DecidableEq E] (μ : ConfigSpace E → ℝ) {n : ℕ}
    (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) (t : ℕ) :
    (∫ U, truncInd μ σ f U (t + 1) * (fun _ => (1 : ℝ)) U ∂(cube n))
      = ∫ A, acp_truncHead μ σ f t A
          * (∫ B, (fun _ => (1 : ℝ)) (acp_join t A B) ∂(ubfTail n t)) ∂(ubfHead n t) :=
  ofh_factor_one_component μ σ f t (G := fun _ => 1) measurable_const (CG := 1)
    (fun _ => by simp)

-- The same factorization for the step-zero truncation on `K₂`.
example {n : ℕ} (σ : Fin n ≃ Sym2 (Fin 2)) :
    (∫ U, truncInd (MonotonicFK.fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) σ
        (Lindeberg.coord s(0, 1)) U (0 + 1) * (fun _ => (1 : ℝ)) U ∂(cube n))
      = ∫ A, acp_truncHead (MonotonicFK.fkMass ⊤ (1 / 2) 2) σ (Lindeberg.coord s(0, 1)) 0 A
          * (∫ B, (fun _ => (1 : ℝ)) (acp_join 0 A B) ∂(ubfTail n 0)) ∂(ubfHead n 0) :=
  ofh_factor_one_component _ σ _ 0 (G := fun _ => 1) measurable_const (CG := 1)
    (fun _ => by simp)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.FactorOneComponent
