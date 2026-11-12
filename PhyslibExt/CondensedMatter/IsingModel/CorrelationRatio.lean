/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.CurrentWeight

/-!
# Correlation ratios in the random-current representation

Positivity of current sums and the ratio bound used in the Aizenman–Barsky–Fernández argument.

## i. Overview

In the random-current representation, `⟨σ_A⟩ = Z_A / Z_∅` where `Z_A` sums current weights with
sources `A`. The current sums are nonnegative, `Z_∅ > 0`, and `Z_A = ⟨σ_A⟩ Z_∅`. With a Griffiths
bound `⟨σ_A⟩ ≤ e` this gives `e · Z_A ≥ ⟨σ_A⟩² Z_∅`.

## ii. Key results

- `StatMech.Ising.acr_currentSum_empty_pos` : `Z_∅ > 0`
- `acw_currentSum_eq_expectation` : `Z_A = ⟨σ_A⟩ Z_∅`
- `StatMech.Ising.acr_claim1_ratio_lower_bound` : the ratio lower bound

## iii. Table of contents

- A. Positivity of current sums
- B. Correlations as ratios
- C. The ratio bound

## iv. References

- M. Aizenman, *Geometric analysis of φ⁴ fields and Ising models. Parts I and II*, Comm. Math. Phys.
  86 (1982) 1–48
- M. Aizenman, D. J. Barsky and R. Fernández, *The phase transition in a general class of Ising-type
  models is sharp*, J. Stat. Phys. 47 (1987) 343–374
-/

@[expose] public section

open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

namespace StatMech

namespace Ising

open StatMech.Sharpness
open StatMech.Sharpness.RandomCurrent

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## A. Positivity of current sums -/

lemma acr_currentSum_nonneg (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (A : Finset V) : 0 ≤ Sharpness.currentSum G β J A := by
  unfold Sharpness.currentSum
  refine tsum_nonneg (fun m => ?_)
  by_cases h : Sharpness.sources G (Sharpness.ofEdgeFun G m) = A
  · rw [ite_eq_left h]
    exact Finset.prod_nonneg (fun e _ =>
      div_nonneg (pow_nonneg (mul_nonneg hβ (hJ e)) _) (by positivity))
  · rw [ite_eq_right h]

lemma acr_currentSum_empty_pos (β : ℝ) (J : Sym2 V → ℝ) :
    0 < Sharpness.currentSum G β J ∅ := by
  have h := Sharpness.partitionJ_eq_currentSum G β J
  have hpos := Sharpness.partitionJ_pos G β J
  rw [h] at hpos
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (Fintype.card V) := by positivity
  nlinarith [hpos, h2]

lemma acr_expectationJ_nonneg (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (A : Finset V) : 0 ≤ Sharpness.expectationJ G β J A := by
  rw [Sharpness.current_representation]
  exact div_nonneg (acr_currentSum_nonneg G β J hβ hJ A) (acr_currentSum_nonneg G β J hβ hJ ∅)

/-! ## B. Correlations as ratios -/

lemma acr_eq15_insertion' (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) :
    Sharpness.currentSum G β J A
      = Sharpness.expectationJ G β J A * Sharpness.currentSum G β J ∅ :=
  acw_currentSum_eq_expectation G β J A (ne_of_gt (acr_currentSum_empty_pos G β J))

lemma acr_eq15_insertion_sq (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V)
    (h0 : Sharpness.currentSum G β J ∅ ≠ 0) :
    Sharpness.expectationJ G β J A * Sharpness.currentSum G β J A
      = (Sharpness.expectationJ G β J A) ^ 2 * Sharpness.currentSum G β J ∅ := by
  rw [acw_currentSum_eq_expectation G β J A h0]; ring

/-! ## C. The ratio bound -/

lemma acr_claim1_griffiths_step (eS cS eΛ : ℝ)
    (hSnn : 0 ≤ eS) (hcSnn : 0 ≤ cS) (hgriff : eS ≤ eΛ) :
    eΛ * (eS * cS) ≥ eS ^ 2 * cS := by
  have hrw : eS ^ 2 * cS = (eS * cS) * eS := by ring
  rw [hrw, ge_iff_le, mul_comm eΛ (eS * cS)]
  exact mul_le_mul_of_nonneg_left hgriff (mul_nonneg hSnn hcSnn)

lemma acr_claim1_ratio_lower_bound (GS : SimpleGraph V) [DecidableRel GS.Adj] (βS : ℝ)
    (JS : Sym2 V → ℝ) (Asrc : Finset V) (eΛ : ℝ)
    (hβ : 0 ≤ βS) (hJ : ∀ e, 0 ≤ JS e)
    (h0 : Sharpness.currentSum GS βS JS ∅ ≠ 0)
    (hgriff : Sharpness.expectationJ GS βS JS Asrc ≤ eΛ) :
    eΛ * Sharpness.currentSum GS βS JS Asrc
      ≥ (Sharpness.expectationJ GS βS JS Asrc) ^ 2 * Sharpness.currentSum GS βS JS ∅ := by
  rw [acw_currentSum_eq_expectation GS βS JS Asrc h0]
  exact acr_claim1_griffiths_step (Sharpness.expectationJ GS βS JS Asrc)
    (Sharpness.currentSum GS βS JS ∅) eΛ
    (acr_expectationJ_nonneg GS βS JS hβ hJ Asrc)
    (acr_currentSum_nonneg GS βS JS hβ hJ ∅) hgriff

end Ising

end StatMech
