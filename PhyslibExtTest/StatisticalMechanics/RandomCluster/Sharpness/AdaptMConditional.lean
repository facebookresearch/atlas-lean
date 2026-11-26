/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.AdaptMConditional

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.AdaptMConditional`

* `truncInd` vanishes after step `0` for a constant observable (the procedure stops at once);
* non-vacuity of `AdaptStepCovBound`: it holds for every constant observable;
* `fk_q2_osss_sharp_of_adaptStepCovBound` on the complete graph on `Fin 2` at `p = 1/2` for the
  constant observable `1/2`, with the step bound discharged by the non-vacuity witness;
* `var_le_trunc_telescope` for the random-cluster mass on `K₂` at `p = 1/2`, `q = 2`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.AdaptMConditional

open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.AdaptMConditional
open _root_.StatMech.OSSS.MonotonicFK _root_.StatMech.OSSS.Coding MeasureTheory

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- For a constant observable the procedure stops at step `0`, so `truncInd` vanishes after it. -/
theorem truncInd_const_succ (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E) (c : ℝ)
    (U : Fin n → ℝ) (t : ℕ) : truncInd μ σ (fun _ => c) U (t + 1) = 0 := by
  have h0 : stopVal μ σ (fun _ => c) U = 0 :=
    (Nat.find_eq_zero _).2 fun _ _ => rfl
  simp [truncInd, h0]

/-- Non-vacuity: `AdaptStepCovBound` holds for every constant observable. -/
theorem adaptStepCovBound_const (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E) (c : ℝ) :
    AdaptStepCovBound μ σ (fun _ => c) := by
  intro t _
  simp [truncInd_const_succ]

-- The conditional OSSS inequality on `K₂` at `p = 1/2`, for the constant observable `1/2`.
example {n : ℕ} (σ : Fin n ≃ Sym2 (Fin 2)) :
    Lindeberg.var (fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) (fun _ => 1 / 2)
      ≤ ∑ e, revealAdapt (fkMass ⊤ (1 / 2) 2) σ (fun _ => 1 / 2) e
          * Lindeberg.cov (fkMass ⊤ (1 / 2) 2) (fun _ => 1 / 2) (Lindeberg.coord e) :=
  fk_q2_osss_sharp_of_adaptStepCovBound ⊤ (by norm_num) (by norm_num) σ
    (fun _ => by norm_num) (fun _ => by norm_num) (adaptStepCovBound_const _ σ _)

-- The variance is bounded by the truncation telescope for the random-cluster mass on `K₂`.
example {n : ℕ} (σ : Fin n ≃ Sym2 (Fin 2)) {f : ConfigSpace (Sym2 (Fin 2)) → ℝ}
    (hf0 : 0 ≤ f) (hf1 : ∀ ω, f ω ≤ 1) :
    Lindeberg.var (fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) f
      ≤ (1 / 2) * ∑ t ∈ Finset.range n,
          ∫ p, |f (codeMap (fkMass ⊤ (1 / 2) 2) (σ : Fin n → Sym2 (Fin 2))
                  (adaptWt p.1 p.2 (stopVal (fkMass ⊤ (1 / 2) 2) σ f p.1) (t + 1)))
                - f (codeMap (fkMass ⊤ (1 / 2) 2) (σ : Fin n → Sym2 (Fin 2))
                  (adaptWt p.1 p.2 (stopVal (fkMass ⊤ (1 / 2) 2) σ f p.1) t))|
                * truncInd (fkMass ⊤ (1 / 2) 2) σ f p.1 (t + 1)
            ∂((GrandCoupling.Vcube n).prod (GrandCoupling.Vcube n)) :=
  var_le_trunc_telescope (fkMass_pos ⊤ (by norm_num) (by norm_num) (by norm_num))
    (fkMass_sum_eq_one ⊤ (by norm_num) (by norm_num) (by norm_num)) σ hf0 hf1

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.AdaptMConditional
