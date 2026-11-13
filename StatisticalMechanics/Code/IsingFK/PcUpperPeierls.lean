/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.Ising.OuterContourWindingClose
import Code.IsingFK.HisingBoxClose
import Code.FK.PcUpperUncond
import Code.FK.ThetaZeroBelowPc

open MeasureTheory Filter Topology

namespace StatMech
namespace IsingFK

open StatMech.Ising StatMech.FK



theorem pup_fvMagnetization_eq_fvMagOrigin (n : ℕ) (β : ℝ) :
    fvMagnetization 2 β n =
      fvMagOrigin (plusField 2) n (bondFinsetTouch 2 n) β 0 := by
  rw [fvMagnetization, fvMagOrigin_plus_eq_integral]
  rfl




theorem pup_fkPc_le_of_fkTheta_pos {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hθ : 0 < fkTheta 2 hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2)) :
    fkPc 2 2 ≤ p := by
  apply csSup_le (fkSubcriticalSet_nonempty (q := 2) (by norm_num))
  intro r hr
  obtain ⟨hr0, hr1, _hq, hrzero⟩ := hr
  by_contra hnot
  have hpr : p < r := lt_of_not_ge hnot
  have hmono : fkTheta 2 hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) ≤
      fkTheta 2 hr0 hr1 (by norm_num : (0 : ℝ) < 2) (q := 2) :=
    tzp_fkTheta_monotone_in_p hp hp1 hr0 hr1 hpr.le
  rw [hrzero] at hmono
  linarith




theorem pup_exists_uniform_fvMagnetization :
    ∃ β > 0, ∃ c > 0, ∀ n, c ≤ fvMagnetization 2 β n := by
  obtain ⟨β₂, hβ₂⟩ := pcl_exists_beta_ratio_lt_one 2
  obtain ⟨β₃, hβ₃⟩ := poc_exists_beta_two_peierlsBound_lt_half 2
  let β := max (max β₂ β₃) 1
  have hβpos : 0 < β := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hβ₂le : β₂ ≤ β := le_trans (le_max_left _ _) (le_max_left _ _)
  have hβ₃le : β₃ ≤ β := le_trans (le_max_right _ _) (le_max_left _ _)
  have hratio : peierlsRatio 2 β < 1 := hβ₂ β hβ₂le
  have hboundlt : twoPeierlsBound 2 β < 1 / 2 := hβ₃ β hβ₃le
  let c := 1 - 2 * twoPeierlsBound 2 β
  have hcpos : 0 < c := by dsimp [c]; linarith
  refine ⟨β, hβpos, c, hcpos, fun n => ?_⟩
  have hprob : probOriginMinus (plusField 2) n (bondFinsetTouch 2 n) β 0 ≤
      twoPeierlsBound 2 β :=
    outerProbOriginMinus_le_two_peierls n β hratio
      (spinCompatibleFill_outerContourWinding n)
  rw [pup_fvMagnetization_eq_fvMagOrigin,
    fvMagOrigin_eq_one_sub_two_mul_probOriginMinus]
  dsimp [c]
  linarith



theorem pup_exists_positive_magnetization :
    ∃ β > 0, 0 < magnetization 2 β := by
  obtain ⟨β, hβ, c, hc, hfinite⟩ := pup_exists_uniform_fvMagnetization
  obtain ⟨φ, _hφ, hlim⟩ := magnetization_eq_limit 2 β
  have hclim : c ≤ magnetization 2 β :=
    ge_of_tendsto hlim (Filter.Eventually.of_forall (fun n => hfinite (φ n)))
  exact ⟨β, hβ, lt_of_lt_of_le hc hclim⟩


theorem fkPc_two_two_lt_one : fkPc 2 2 < 1 := by
  obtain ⟨β, hβ, hmag⟩ := pup_exists_positive_magnetization
  have hp : 0 < pOfBeta β := pOfBeta_pos hβ
  have hp1 : pOfBeta β < 1 := pOfBeta_lt_one β
  have hid : magnetization 2 β =
      fkTheta 2 hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) :=
    mfc_magPercoId 2 (by norm_num) (hbx_hisingBox 2) β hβ hp hp1
  have hθ : 0 < fkTheta 2 hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) := by
    rwa [← hid]
  exact lt_of_le_of_lt (pup_fkPc_le_of_fkTheta_pos hp hp1 hθ) hp1





theorem ising_transition_two_at_fkPc :
    0 < pToBeta 2 (fkPc 2 2) ∧
      (∀ β, 0 < β → β < pToBeta 2 (fkPc 2 2) → magnetization 2 β = 0) ∧
      (∀ β, pToBeta 2 (fkPc 2 2) < β → 0 < magnetization 2 β) := by
  let pc := fkPc 2 2
  let βc := pToBeta 2 pc
  change 0 < βc ∧
    (∀ β, 0 < β → β < βc → magnetization 2 β = 0) ∧
    (∀ β, βc < β → 0 < magnetization 2 β)
  have hpc0 : 0 < pc := fkPc_pos_of_two_le (le_refl 2) (by norm_num)
  have hpc1 : pc < 1 := fkPc_two_two_lt_one
  have hβc : 0 < βc := pToBeta_two_pos hpc0 hpc1
  refine ⟨hβc, ?_, ?_⟩
  · intro β hβ hβlt
    have hp : 0 < pOfBeta β := pOfBeta_pos hβ
    have hp1 : pOfBeta β < 1 := pOfBeta_lt_one β
    have hparam : pOfBeta β < pc := by
      apply ((strictMonoOn_pToBeta 2 (by norm_num)).lt_iff_lt
        (Set.mem_Iio.mpr hp1) (Set.mem_Iio.mpr hpc1)).mp
      rw [fkRoute_pToBeta_pOfBeta]
      exact hβlt
    have hzero : fkTheta 2 hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0 :=
      tzp_fkTheta_eq_zero_of_lt_pc hp hp1 hparam
    have hid := mfc_magPercoId 2 (by norm_num) (hbx_hisingBox 2) β hβ hp hp1
    exact hid.trans hzero
  · intro β hβgt
    have hβ : 0 < β := lt_trans hβc hβgt
    have hp : 0 < pOfBeta β := pOfBeta_pos hβ
    have hp1 : pOfBeta β < 1 := pOfBeta_lt_one β
    have hparam : pc < pOfBeta β :=
      (fkPc_lt_pOfBeta_iff 2 hβ hpc1).mpr hβgt
    have hθ := fkTheta_pos_of_fkPc_lt 2 hp hp1 hparam
    have hid := mfc_magPercoId 2 (by norm_num) (hbx_hisingBox 2) β hβ hp hp1
    rwa [hid]


theorem ising_transition_two_unconditional :
    ∃ βc : ℝ, 0 < βc ∧
      (∀ β, 0 < β → β < βc → magnetization 2 β = 0) ∧
      (∀ β, βc < β → 0 < magnetization 2 β) :=
  ⟨pToBeta 2 (fkPc 2 2), ising_transition_two_at_fkPc⟩




theorem isingBetaC_two_eq_fkPc :
    betaC (magnetization 2) = -(1 / 2) * Real.log (1 - fkPc 2 2) := by
  let βc := pToBeta 2 (fkPc 2 2)
  obtain ⟨hβc, hbelow, habove⟩ := ising_transition_two_at_fkPc
  let S : Set ℝ := {β : ℝ | 0 < β ∧ magnetization 2 β = 0}
  have hub : ∀ β ∈ S, β ≤ βc := by
    intro β hβS
    by_contra hnot
    have hgt : βc < β := lt_of_not_ge hnot
    have hpos := habove β hgt
    exact (ne_of_gt hpos) hβS.2
  have hbdd : BddAbove S := ⟨βc, hub⟩
  have hwit : βc / 2 ∈ S := by
    refine ⟨by linarith, hbelow _ (by linarith) (by linarith)⟩
  have hsup_le : sSup S ≤ βc := csSup_le ⟨βc / 2, hwit⟩ hub
  have hle_sup : βc ≤ sSup S := by
    apply le_of_forall_lt_imp_le_of_dense
    intro a ha
    by_cases ha0 : a ≤ 0
    · exact ha0.trans (le_trans (by linarith : (0 : ℝ) ≤ βc / 2) (le_csSup hbdd hwit))
    · have ha_pos : 0 < a := lt_of_not_ge ha0
      exact le_csSup hbdd ⟨ha_pos, hbelow a ha_pos ha⟩
  have hs : sSup S = βc := le_antisymm hsup_le hle_sup
  unfold betaC
  change sSup S = _
  rw [hs, show βc = pToBeta 2 (fkPc 2 2) from rfl, pToBeta_two]

end IsingFK
end StatMech
