/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





























































import Mathlib
import Code.Ising.InfiniteVolume
import Code.Ising.Peierls
import Code.Lattice.PlanarTopology

open MeasureTheory Filter Topology Finset SimpleGraph
open scoped BigOperators ENNReal

namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}












noncomputable def peierlsBound (d : ℕ) (β : ℝ) : ℝ :=
  ∑' ℓ : ℕ, (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ * Real.exp (-(2 * β) * ℓ)


noncomputable def peierlsRatio (d : ℕ) (β : ℝ) : ℝ := (2 * d : ℝ) * Real.exp (-(2 * β))

@[simp] lemma peierlsRatio_def (d : ℕ) (β : ℝ) :
    peierlsRatio d β = (2 * d : ℝ) * Real.exp (-(2 * β)) := rfl


lemma peierlsRatio_nonneg (d : ℕ) (β : ℝ) : 0 ≤ peierlsRatio d β := by
  unfold peierlsRatio; positivity


lemma peierlsSummand_eq (d : ℕ) (β : ℝ) (ℓ : ℕ) :
    (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ * Real.exp (-(2 * β) * ℓ)
      = (ℓ : ℝ) * (peierlsRatio d β) ^ ℓ := by
  rw [peierlsRatio_def, mul_assoc]
  congr 1
  conv_rhs => rw [mul_pow, ← Real.exp_nat_mul]
  rw [mul_comm (ℓ : ℝ) (-(2 * β))]



lemma peierlsBound_eq_closedForm (d : ℕ) (β : ℝ)
    (hx : ‖peierlsRatio d β‖ < 1) :
    peierlsBound d β = (peierlsRatio d β) / (1 - peierlsRatio d β) ^ 2 := by
  unfold peierlsBound
  rw [show (fun ℓ : ℕ => (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ * Real.exp (-(2 * β) * ℓ))
        = (fun ℓ : ℕ => (ℓ : ℝ) * (peierlsRatio d β) ^ ℓ) from
      funext (peierlsSummand_eq d β)]
  exact tsum_coe_mul_geometric_of_norm_lt_one hx


lemma peierlsRatio_tendsto_atTop (d : ℕ) :
    Tendsto (fun β : ℝ => peierlsRatio d β) atTop (nhds 0) := by
  have h1 : Tendsto (fun β : ℝ => Real.exp (-(2 * β))) atTop (nhds 0) := by
    apply Real.tendsto_exp_atBot.comp
    apply tendsto_atBot.2
    intro b
    filter_upwards [eventually_ge_atTop (-b / 2)] with β hβ
    nlinarith
  have := h1.const_mul (2 * d : ℝ)
  simpa [peierlsRatio] using this


lemma closedForm_tendsto_zero :
    Tendsto (fun x : ℝ => x / (1 - x) ^ 2) (nhds 0) (nhds 0) := by
  have : Tendsto (fun x : ℝ => x / (1 - x) ^ 2) (nhds 0) (nhds (0 / (1 - 0) ^ 2)) := by
    apply Tendsto.div tendsto_id (Continuous.tendsto (by fun_prop) 0)
    norm_num
  simpa using this



lemma peierlsBound_tendsto_atTop (d : ℕ) :
    Tendsto (fun β : ℝ => peierlsBound d β) atTop (nhds 0) := by
  have hev : (fun β : ℝ => peierlsBound d β) =ᶠ[atTop]
      (fun β : ℝ => (peierlsRatio d β) / (1 - peierlsRatio d β) ^ 2) := by
    have hlt : ∀ᶠ β in atTop, peierlsRatio d β < 1 :=
      (peierlsRatio_tendsto_atTop d).eventually
        (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [hlt] with β hβ
    refine peierlsBound_eq_closedForm d β ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (peierlsRatio_nonneg d β)]
    exact hβ
  rw [tendsto_congr' hev]
  simpa using closedForm_tendsto_zero.comp (peierlsRatio_tendsto_atTop d)





theorem exists_beta_peierlsBound_lt_half (d : ℕ) :
    ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β → peierlsBound d β < 1 / 2 := by
  have h := (peierlsBound_tendsto_atTop d).eventually
    (eventually_lt_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  rw [eventually_atTop] at h
  obtain ⟨β₀, hβ₀⟩ := h
  exact ⟨β₀, hβ₀⟩


lemma peierlsBound_nonneg (d : ℕ) (β : ℝ) : 0 ≤ peierlsBound d β := by
  unfold peierlsBound
  apply tsum_nonneg
  intro ℓ
  positivity













lemma contour_card_le (d : ℕ) (B : Finset (Site d)) (ℓ : ℕ) (hB : B.card ≤ ℓ) :
    ((B.sigma (fun v => (hypercubicLattice d).finsetWalkLength ℓ v v)).card : ℝ)
      ≤ (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ := by
  have h1 := card_circuits_based_in_le_pow d B ℓ
  have h3 : ((B.sigma (fun v => (hypercubicLattice d).finsetWalkLength ℓ v v)).card : ℕ)
      ≤ ℓ * (2 * d) ^ ℓ := le_trans h1 (Nat.mul_le_mul_right _ hB)
  calc ((B.sigma (fun v => (hypercubicLattice d).finsetWalkLength ℓ v v)).card : ℝ)
      ≤ ((ℓ * (2 * d) ^ ℓ : ℕ) : ℝ) := by exact_mod_cast h3
    _ = (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ := by push_cast; ring






lemma contour_card_le_peierlsSummand (d : ℕ) (β : ℝ) (B : Finset (Site d)) (ℓ : ℕ)
    (hB : B.card ≤ ℓ) :
    ((B.sigma (fun v => (hypercubicLattice d).finsetWalkLength ℓ v v)).card : ℝ)
        * Real.exp (-(2 * β) * ℓ)
      ≤ (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ * Real.exp (-(2 * β) * ℓ) := by
  apply mul_le_mul_of_nonneg_right (contour_card_le d B ℓ hB) (le_of_lt (Real.exp_pos _))










noncomputable def probOriginMinus (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β h : ℝ) : ℝ :=
  ∑ τ : {x // x ∈ box d n} → Bool,
    (if (glue η τ) (origin d) = false then fvProb η n B β h τ else 0)


lemma probOriginMinus_nonneg (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β h : ℝ) :
    0 ≤ probOriginMinus η n B β h := by
  unfold probOriginMinus
  apply Finset.sum_nonneg
  intro τ _
  split
  · exact fvProb_nonneg η n B β h τ
  · exact le_refl 0




lemma fvMagOrigin_eq_one_sub_two_mul_probOriginMinus (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β h : ℝ) :
    fvMagOrigin η n B β h = 1 - 2 * probOriginMinus η n B β h := by
  unfold fvMagOrigin probOriginMinus
  rw [Finset.mul_sum, ← fvProb_sum_eq_one η n B β h, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  unfold spin
  by_cases hb : (glue η τ) (origin d) = true <;> simp [hb]; ring




lemma fvMagOrigin_pos_of_probOriginMinus_lt_half (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β h : ℝ)
    (hP : probOriginMinus η n B β h < 1 / 2) :
    0 < fvMagOrigin η n B β h := by
  rw [fvMagOrigin_eq_one_sub_two_mul_probOriginMinus]
  linarith
















def PeierlsContourBound (d n : ℕ) (β : ℝ) : Prop :=
  probOriginMinus (plusField d) n (bondFinsetTouch d n) β 0 ≤ peierlsBound d β













theorem peierls_long_range_order (hd : 2 ≤ d) :
    ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β →
      PeierlsContourBound d n β →
        plusMeasure d n β 0 ≠ minusMeasure d n β 0 := by
  obtain ⟨β₀, hβ₀⟩ := exists_beta_peierlsBound_lt_half d
  refine ⟨β₀, fun n β hβ hContour => ?_⟩
  
  have hPlt : probOriginMinus (plusField d) n (bondFinsetTouch d n) β 0 < 1 / 2 :=
    lt_of_le_of_lt hContour (hβ₀ β hβ)
  
  have hmag : 0 < fvMagOrigin (plusField d) n (bondFinsetTouch d n) β 0 :=
    fvMagOrigin_pos_of_probOriginMinus_lt_half _ _ _ _ _ hPlt
  
  exact peierls_lro_criterion hd n β hmag






theorem peierls_long_range_order' (hd : 2 ≤ d)
    (hGeom : ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β → PeierlsContourBound d n β) :
    ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β →
      plusMeasure d n β 0 ≠ minusMeasure d n β 0 := by
  obtain ⟨β₁, hβ₁⟩ := exists_beta_peierlsBound_lt_half d
  obtain ⟨β₂, hβ₂⟩ := hGeom
  refine ⟨max β₁ β₂, fun n β hβ => ?_⟩
  have h1 : β₁ ≤ β := le_trans (le_max_left _ _) hβ
  have h2 : β₂ ≤ β := le_trans (le_max_right _ _) hβ
  have hPlt : probOriginMinus (plusField d) n (bondFinsetTouch d n) β 0 < 1 / 2 :=
    lt_of_le_of_lt (hβ₂ n β h2) (hβ₁ β h1)
  have hmag : 0 < fvMagOrigin (plusField d) n (bondFinsetTouch d n) β 0 :=
    fvMagOrigin_pos_of_probOriginMinus_lt_half _ _ _ _ _ hPlt
  exact peierls_lro_criterion hd n β hmag

end Ising

end StatMech
