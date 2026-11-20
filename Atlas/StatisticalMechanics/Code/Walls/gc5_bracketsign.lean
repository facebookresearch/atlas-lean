/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





























































import Mathlib
import Code.Ising.EnsembleGHS

open Finset Classical
open scoped symmDiff BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option maxHeartbeats 800000

namespace StatMech.Walls

open StatMech.Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]















def gc5_bracket (μ P : ℝ) : ℝ := -2 * μ * P






theorem gc5_dep_ursell_eq (β : ℝ) (J : Sym2 V → ℝ) (M : Finset (Current V)) (B : Finset V)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    egh_ensembleUrsell G β J M B o x y = -2 * tcp_allConnMass G β J M B o x y :=
  egh_ensemble_ursell_eq G β J M B hox hoy hxy






theorem gc5_dep_prob_le_one (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Current V)) (B : Finset V) (o x y : V) :
    tcp_allConnProb G β J M B o x y ≤ 1 :=
  egh_ensemble_prob_le_one G β J hβ hJ M B o x y










theorem gc5_allConnMass_le_partition (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Current V)) (B : Finset V) (o x y : V) :
    tcp_allConnMass G β J M B o x y ≤ tcp_partitionFunction G β J M B :=
  tcp_allConnMass_le_partitionFunction G β J hβ hJ M B o x y












theorem gc5_bracket_nonpos {μ P : ℝ} (hμ : 0 ≤ μ) (hP : 0 ≤ P) :
    gc5_bracket μ P ≤ 0 := by
  unfold gc5_bracket
  nlinarith [mul_nonneg hμ hP]





theorem gc5_bracket_ge_neg (μ : ℝ) {P : ℝ} (hμ : 0 ≤ μ) (hP : P ≤ 1) :
    -2 * μ ≤ gc5_bracket μ P := by
  unfold gc5_bracket
  nlinarith [mul_nonneg hμ (sub_nonneg.mpr hP)]










theorem gc5_bracket_sign {μ P : ℝ} (hμ : 0 ≤ μ) (hP0 : 0 ≤ P) (hP1 : P ≤ 1) :
    -2 * μ ≤ gc5_bracket μ P ∧ gc5_bracket μ P ≤ 0 :=
  ⟨gc5_bracket_ge_neg μ hμ hP1, gc5_bracket_nonpos hμ hP0⟩





theorem gc5_bracket_abs_le {μ P : ℝ} (hμ : 0 ≤ μ) (hP0 : 0 ≤ P) (hP1 : P ≤ 1) :
    |gc5_bracket μ P| ≤ 2 * μ := by
  obtain ⟨hlo, hhi⟩ := gc5_bracket_sign hμ hP0 hP1
  rw [abs_le]
  constructor <;> linarith














theorem gc5_prob_mem_Icc (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Current V)) (B : Finset V) (o x y : V) :
    0 ≤ tcp_allConnProb G β J M B o x y ∧ tcp_allConnProb G β J M B o x y ≤ 1 :=
  ⟨tcp_allConn_prob_nonneg G β J hβ hJ M B o x y,
   egh_ensemble_prob_le_one G β J hβ hJ M B o x y⟩











theorem gc5_bracket_sign_ensemble (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Current V)) (B : Finset V) (o x y : V) {μ : ℝ} (hμ : 0 ≤ μ) :
    -2 * μ ≤ gc5_bracket μ (tcp_allConnProb G β J M B o x y)
      ∧ gc5_bracket μ (tcp_allConnProb G β J M B o x y) ≤ 0 := by
  obtain ⟨hP0, hP1⟩ := gc5_prob_mem_Icc G β J hβ hJ M B o x y
  exact gc5_bracket_sign hμ hP0 hP1






theorem gc5_bracket_eq_headline (β : ℝ) (J : Sym2 V → ℝ) (M : Finset (Current V)) (B : Finset V)
    (o x y : V) (μ : ℝ) :
    gc5_bracket μ (tcp_allConnProb G β J M B o x y)
      = -2 * μ * tcp_allConnProb G β J M B o x y := rfl













theorem gc5_bracket_at_one (μ : ℝ) : gc5_bracket μ 1 = -2 * μ := by
  unfold gc5_bracket; ring




theorem gc5_bracket_at_zero (μ : ℝ) : gc5_bracket μ 0 = 0 := by
  unfold gc5_bracket; ring







theorem gc5_bracket_free_range {μ t : ℝ} (hμ : 0 ≤ μ) (hlo : -2 * μ ≤ t) (hhi : t ≤ 0) :
    ∃ P : ℝ, 0 ≤ P ∧ P ≤ 1 ∧ gc5_bracket μ P = t := by
  rcases eq_or_lt_of_le hμ with hμ0 | hμpos
  · 
    refine ⟨0, le_refl 0, zero_le_one, ?_⟩
    have ht : t = 0 := le_antisymm hhi (by rw [← hμ0] at hlo; linarith)
    rw [gc5_bracket_at_zero, ht]
  · 
    refine ⟨-t / (2 * μ), ?_, ?_, ?_⟩
    · apply div_nonneg (by linarith) (by linarith)
    · rw [div_le_one (by linarith)]; linarith
    · unfold gc5_bracket
      have h2μ : (2 : ℝ) * μ ≠ 0 := ne_of_gt (by linarith)
      rw [show -2 * μ * (-t / (2 * μ)) = (2 * μ) * (t / (2 * μ)) by ring,
        mul_div_cancel₀ t h2μ]









theorem gc5_bracket_sign_at_zero {μ : ℝ} (hμ : 0 ≤ μ) :
    -2 * μ ≤ gc5_bracket μ 0 ∧ gc5_bracket μ 0 ≤ 0 :=
  gc5_bracket_sign hμ (le_refl 0) zero_le_one



theorem gc5_bracket_sign_at_one {μ : ℝ} (hμ : 0 ≤ μ) :
    -2 * μ ≤ gc5_bracket μ 1 ∧ gc5_bracket μ 1 ≤ 0 :=
  gc5_bracket_sign hμ zero_le_one (le_refl 1)

end StatMech.Walls
