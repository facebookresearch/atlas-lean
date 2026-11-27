/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.AdaptFiberCross

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.AdaptFiberCross`

* non-vacuity of `acp_TailCondLaw`: it holds for the empty revealment order on `Fin 0`;
* `acp_truncInd_factors` and `acp_truncHead_le_one` for the random-cluster mass on the complete
  graph on `Fin 2` at `p = 1/2`, `q = 2`;
* `acp_fiberCross_le_one` for the observable "edge `s(0, 1)` is open" on `K₂`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.AdaptFiberCross

open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.AdaptDisintegration
open _root_.StatMech.OSSS.AdaptMConditional _root_.StatMech.OSSS.MonotonicFK

-- Non-vacuity: the tail conditional law holds (vacuously) for the empty order.
example (μ : ConfigSpace (Fin 0) → ℝ) (f : ConfigSpace (Fin 0) → ℝ) :
    acp_TailCondLaw μ (Equiv.refl (Fin 0)) f :=
  fun t htn => absurd htn (Nat.not_lt_zero t)

-- The truncation indicator factors through the head coordinates, for the FK mass on `K₂`.
example {n : ℕ} (σ : Fin n ≃ Sym2 (Fin 2)) (f : ConfigSpace (Sym2 (Fin 2)) → ℝ) (t : ℕ)
    (U : Fin n → ℝ) :
    truncInd (fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) σ f U (t + 1) =
      acp_truncHead (fkMass ⊤ (1 / 2) 2) σ f t ((ubfSplit n t U).1) ∧
    |acp_truncHead (fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) σ f t
        ((ubfSplit n t U).1)| ≤ 1 :=
  ⟨acp_truncInd_factors _ σ f t U, acp_truncHead_le_one _ σ f t _⟩

-- The fiber cross term of the open-edge observable on `K₂` is bounded by `1`.
example {n : ℕ} (σ : Fin n ≃ Sym2 (Fin 2)) (e : Sym2 (Fin 2)) (s₁ s₂ : ℕ) (U : Fin n → ℝ) :
    |fiberCross (fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) σ
        (fun ω => if ω s(0, 1) then 1 else 0) e s₁ s₂ U| ≤ 1 :=
  acp_fiberCross_le_one _ σ (fun ω => by split_ifs <;> norm_num) e s₁ s₂ U

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.AdaptFiberCross
