/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.AdaptDisintegration

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.AdaptDisintegration`

* `sw2_invol` evaluated on an explicit point of `Fin 3 ⊕ Fin 3`;
* non-vacuity of `AdaptCondBBB`: it holds for every constant observable;
* `adsD_adaptStepCovBound_of_condBBB` for the random-cluster mass on `K₂` at `p = 1/2`, `q = 2`;
* `adsD_fk_q2_sharp` on the complete graph on `Fin 2` at `p = 1/2` for the constant observable
  `1/2`, with `AdaptCondBBB` discharged by the non-vacuity witness.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.AdaptDisintegration

open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.AdaptDisintegration
open _root_.StatMech.OSSS.AdaptMConditional _root_.StatMech.OSSS.MonotonicFK MeasureTheory

variable {E : Type*} [Fintype E] [DecidableEq E]

-- `sw2` is an involution; on `inl 0` with `s = 1` it swaps sides.
example : sw2 3 1 2 (sw2 3 1 2 (Sum.inl 0)) = Sum.inl 0 ∧ sw2 3 1 2 (Sum.inl 0) = Sum.inr 0 :=
  ⟨sw2_invol 3 1 2 _, by decide⟩

/-- Non-vacuity: `AdaptCondBBB` holds for every constant observable (the procedure stops at once,
  so every truncation indicator after step `0` vanishes). -/
theorem adaptCondBBB_const (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E) (c : ℝ) :
    AdaptCondBBB μ σ (fun _ => c) := by
  have h : ∀ U t, truncInd μ σ (fun _ => c) U (t + 1) = 0 := fun U t => by
    have h0 : stopVal μ σ (fun _ => c) U = 0 := (Nat.find_eq_zero _).2 fun _ _ => rfl
    simp [truncInd, h0]
  intro t _
  simp [h]

-- `AdaptCondBBB` gives the step covariance bound for the random-cluster mass on `K₂`.
example {n : ℕ} (σ : Fin n ≃ Sym2 (Fin 2)) {f : ConfigSpace (Sym2 (Fin 2)) → ℝ}
    (hf : Monotone f) (hfC : ∀ ω, |f ω| ≤ 1)
    (hBBB : AdaptCondBBB (fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) σ f) :
    AdaptStepCovBound (fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) σ f :=
  adsD_adaptStepCovBound_of_condBBB (fkMass_pos ⊤ (by norm_num) (by norm_num) (by norm_num))
    (fkMass_isMonotonic ⊤ (by norm_num) (by norm_num) (by norm_num)) σ hf hfC hBBB

-- The conditional OSSS inequality on `K₂` at `p = 1/2`, for the constant observable `1/2`.
example {n : ℕ} (σ : Fin n ≃ Sym2 (Fin 2)) :
    Lindeberg.var (fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) (fun _ => 1 / 2)
      ≤ ∑ e, revealAdapt (fkMass ⊤ (1 / 2) 2) σ (fun _ => 1 / 2) e
          * Lindeberg.cov (fkMass ⊤ (1 / 2) 2) (fun _ => 1 / 2) (Lindeberg.coord e) :=
  adsD_fk_q2_sharp ⊤ (by norm_num) (by norm_num) σ monotone_const (fun _ => by norm_num)
    (fun _ => by norm_num) (adaptCondBBB_const _ σ _)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.AdaptDisintegration
