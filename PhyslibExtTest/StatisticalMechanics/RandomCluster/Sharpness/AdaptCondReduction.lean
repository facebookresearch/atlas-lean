/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.AdaptCondReduction

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.AdaptCondReduction`

* `otc_adaptCondBBB_of_tailCondLaw` applied to the random-cluster mass on the complete graph on
  `Fin 2` at `p = 1/2`, `q = 2`, conditional on the tail conditional law;
* `otc_adaptCondBBB_of_tailCondLaw` applied end to end on the empty order on `Fin 0`, where the
  tail conditional law holds;
* `otc_truncHead_nonneg` and `otc_delta_eq` for the random-cluster mass on `K₂`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.AdaptCondReduction

open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.AdaptDisintegration
open _root_.StatMech.OSSS.AdaptMConditional _root_.StatMech.OSSS.MonotonicFK MeasureTheory

-- The tail conditional law gives `AdaptCondBBB` for the FK mass on `K₂`.
example {n : ℕ} (σ : Fin n ≃ Sym2 (Fin 2)) {f : ConfigSpace (Sym2 (Fin 2)) → ℝ}
    (hfC : ∀ ω, |f ω| ≤ 1)
    (hTCL : acp_TailCondLaw (fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) σ f) :
    AdaptCondBBB (fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) σ f :=
  otc_adaptCondBBB_of_tailCondLaw σ hfC hTCL

-- End to end on the empty order, where the tail conditional law holds.
example (μ : ConfigSpace (Fin 0) → ℝ) :
    AdaptCondBBB μ (Equiv.refl (Fin 0)) (fun _ => 0) :=
  otc_adaptCondBBB_of_tailCondLaw _ (fun _ => by norm_num)
    (fun t htn => absurd htn (Nat.not_lt_zero t))

-- The truncated head is nonnegative and integrates to the truncation mass, on `K₂`.
example {n : ℕ} (σ : Fin n ≃ Sym2 (Fin 2)) (f : ConfigSpace (Sym2 (Fin 2)) → ℝ) (t : ℕ)
    (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
    0 ≤ acp_truncHead (fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) σ f t A ∧
    (∫ U, truncInd (fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) σ f U (t + 1)
        ∂(Probability.cube n))
      = ∫ A, acp_truncHead (fkMass ⊤ (1 / 2) 2) σ f t A ∂(ubfHead n t) :=
  ⟨otc_truncHead_nonneg _ σ f t A, otc_delta_eq _ σ f t⟩

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.AdaptCondReduction
