/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/















































































import Mathlib
import Code.Sharpness.RandomCurrent
import Code.Sharpness.CurrentRep
import Code.Ising.AizenmanInclusionExclusion
import Code.Ising.AizenmanHdom
import Code.Ising.CurrentWeight

open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace StatMech

namespace Ising

open StatMech.Sharpness
open StatMech.Sharpness.RandomCurrent

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]











theorem acr_currentSum_nonneg (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (A : Finset V) : 0 ≤ Sharpness.currentSum G β J A := by
  unfold Sharpness.currentSum
  refine tsum_nonneg (fun m => ?_)
  by_cases h : Sharpness.sources G (Sharpness.ofEdgeFun G m) = A
  · rw [if_pos h]
    exact Finset.prod_nonneg (fun e _ =>
      div_nonneg (pow_nonneg (mul_nonneg hβ (hJ e)) _) (by positivity))
  · rw [if_neg h]







theorem acr_currentSum_empty_pos (β : ℝ) (J : Sym2 V → ℝ) :
    0 < Sharpness.currentSum G β J ∅ := by
  have h := Sharpness.partitionJ_eq_currentSum G β J
  have hpos := Sharpness.partitionJ_pos G β J
  rw [h] at hpos
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (Fintype.card V) := by positivity
  nlinarith [hpos, h2]





theorem acr_expectationJ_nonneg (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (A : Finset V) : 0 ≤ Sharpness.expectationJ G β J A := by
  rw [Sharpness.current_representation]
  exact div_nonneg (acr_currentSum_nonneg G β J hβ hJ A) (acr_currentSum_nonneg G β J hβ hJ ∅)
























theorem acr_eq15_insertion (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V)
    (h0 : Sharpness.currentSum G β J ∅ ≠ 0) :
    Sharpness.currentSum G β J A
      = Sharpness.expectationJ G β J A * Sharpness.currentSum G β J ∅ := by
  rw [Sharpness.current_representation, div_mul_cancel₀ _ h0]







theorem acr_eq15_insertion' (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) :
    Sharpness.currentSum G β J A
      = Sharpness.expectationJ G β J A * Sharpness.currentSum G β J ∅ :=
  acr_eq15_insertion G β J A (ne_of_gt (acr_currentSum_empty_pos G β J))













theorem acr_currentSum_ratio (β : ℝ) (J : Sym2 V → ℝ) (A B : Finset V)
    (h0 : Sharpness.currentSum G β J ∅ ≠ 0) (hA : Sharpness.expectationJ G β J A ≠ 0) :
    Sharpness.currentSum G β J B
      = (Sharpness.expectationJ G β J B / Sharpness.expectationJ G β J A)
        * Sharpness.currentSum G β J A := by
  have hB : Sharpness.currentSum G β J B
      = Sharpness.expectationJ G β J B * Sharpness.currentSum G β J ∅ :=
    acr_eq15_insertion G β J B h0
  have hAeq : Sharpness.currentSum G β J A
      = Sharpness.expectationJ G β J A * Sharpness.currentSum G β J ∅ :=
    acr_eq15_insertion G β J A h0
  rw [hB, hAeq]; field_simp










theorem acr_eq15_insertion_sq (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V)
    (h0 : Sharpness.currentSum G β J ∅ ≠ 0) :
    Sharpness.expectationJ G β J A * Sharpness.currentSum G β J A
      = (Sharpness.expectationJ G β J A) ^ 2 * Sharpness.currentSum G β J ∅ := by
  rw [acr_eq15_insertion G β J A h0]; ring




















theorem acr_claim1_griffiths_step (eS cS eΛ : ℝ)
    (hSnn : 0 ≤ eS) (hcSnn : 0 ≤ cS) (hgriff : eS ≤ eΛ) :
    eΛ * (eS * cS) ≥ eS ^ 2 * cS := by
  have hrw : eS ^ 2 * cS = (eS * cS) * eS := by ring
  rw [hrw, ge_iff_le, mul_comm eΛ (eS * cS)]
  exact mul_le_mul_of_nonneg_left hgriff (mul_nonneg hSnn hcSnn)











theorem acr_claim1_ratio_lower_bound (GS : SimpleGraph V) [DecidableRel GS.Adj] (βS : ℝ)
    (JS : Sym2 V → ℝ) (Asrc : Finset V) (eΛ : ℝ)
    (hβ : 0 ≤ βS) (hJ : ∀ e, 0 ≤ JS e)
    (h0 : Sharpness.currentSum GS βS JS ∅ ≠ 0)
    (hgriff : Sharpness.expectationJ GS βS JS Asrc ≤ eΛ) :
    eΛ * Sharpness.currentSum GS βS JS Asrc
      ≥ (Sharpness.expectationJ GS βS JS Asrc) ^ 2 * Sharpness.currentSum GS βS JS ∅ := by
  rw [acr_eq15_insertion GS βS JS Asrc h0]
  exact acr_claim1_griffiths_step (Sharpness.expectationJ GS βS JS Asrc)
    (Sharpness.currentSum GS βS JS ∅) eΛ
    (acr_expectationJ_nonneg GS βS JS hβ hJ Asrc)
    (acr_currentSum_nonneg GS βS JS hβ hJ ∅) hgriff





















theorem acr_crossClass_closure {ι : Type*} [DecidableEq ι] [Fintype ι]
    (ends : ι → Sym2 V) (M : Finset (Finset ι))
    (hnd : ∀ m ∈ M, ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V)
    (hm : ∀ m ∈ M, Sharpness.RandomCurrent.sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (Φ : Finset ι → Finset ι → ℝ)
    (hΦ : ∀ m ∈ M, ∀ K P, P ⊆ m → K ⊆ m → (Φ m) (K ∆ P) = (Φ m) K)
    (hratio : 2 * (∑ m ∈ M.filter (fun m => aie_allConn ends m o x y), aie_mass ends m (Φ m) A)
      ≤ ∑ m ∈ M.filter (fun m => aie_noneConn ends m o x y), aie_mass ends m (Φ m) A) :
    0 ≤ ∑ m ∈ M, aie_gap ends m (Φ m) A o x y :=
  aie_inclusion_exclusion ends M hnd A hm hox hoy hxy Φ hΦ hratio































theorem acr_ratioDom_refutable :
    ¬ (2 * (∑ m ∈ ({({0, 1, 2} : Finset (Fin 3))} : Finset (Finset (Fin 3))).filter
              (fun m => aie_allConn ahd_triEnds m 0 1 2),
            aie_mass ahd_triEnds m (fun _ => 1)
              (StatMech.Sharpness.RandomCurrent.sources ahd_triEnds
                ({0, 1, 2} : Finset (Fin 3))))
        ≤ ∑ m ∈ ({({0, 1, 2} : Finset (Fin 3))} : Finset (Finset (Fin 3))).filter
              (fun m => aie_noneConn ahd_triEnds m 0 1 2),
            aie_mass ahd_triEnds m (fun _ => 1)
              (StatMech.Sharpness.RandomCurrent.sources ahd_triEnds
                ({0, 1, 2} : Finset (Fin 3)))) :=
  ahd_hdom_refutable

end Ising

end StatMech
