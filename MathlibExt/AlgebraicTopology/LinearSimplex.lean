/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Analysis.Normed.Module.Convex

/-!
# Linear simplex geometry for barycentric subdivision

Barycenters, convex-hull membership, and diameter estimates for linear simplices.
This is the geometric input for barycentric subdivision.

## Main definitions
* `linSimplexBarycenter`

## Main results
* `linSimplexBarycenter_mem_convexHull`
* diameter estimates
-/

@[expose] public section

open scoped BigOperators
open Matrix

namespace AlgebraicTopology

universe u

variable (n : ℕ)

section AffineSimplex

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Barycenter of a linear simplex. -/
noncomputable def linSimplexBarycenter {n : ℕ} (σ : Fin (n + 1) → V) : V :=
  Finset.centroid ℝ Finset.univ σ

lemma linSimplexBarycenter_mem_convexHull {n : ℕ} (σ : Fin (n + 1) → V) :
    linSimplexBarycenter σ ∈ convexHull ℝ (Set.range σ) := by
  rw [linSimplexBarycenter, Finset.centroid_def]
  refine affineCombination_mem_convexHull (fun i _ => ?_) ?_
  · rw [Finset.centroidWeights_apply]
    positivity
  · exact Finset.sum_centroidWeights_eq_one_of_nonempty ℝ _ ⟨0, Finset.mem_univ 0⟩

lemma linSimplexBarycenter_eq_avg {n : ℕ} (σ : Fin (n + 1) → V) :
    linSimplexBarycenter σ = ((n : ℝ) + 1)⁻¹ • ∑ i, σ i := by
  rw [linSimplexBarycenter, Finset.centroid_def, Finset.affineCombination_eq_linear_combination]
  · simp [Finset.centroidWeights_apply, Finset.smul_sum]
  · exact Finset.sum_centroidWeights_eq_one_of_nonempty ℝ _ ⟨0, Finset.mem_univ 0⟩

lemma linSimplexBarycenter_comp_linear {W : Type*}
    [AddCommGroup W] [Module ℝ W] (L : V →ₗ[ℝ] W)
    {n : ℕ} (σ : Fin (n + 1) → V) :
    linSimplexBarycenter (L ∘ σ) = L (linSimplexBarycenter σ) := by
  rw [linSimplexBarycenter_eq_avg, linSimplexBarycenter_eq_avg,
    map_smul, map_sum]
  rfl

lemma linSimplexBarycenter_point (lam : Fin 1 → V) :
    linSimplexBarycenter lam = lam 0 := by
  rw [linSimplexBarycenter_eq_avg, Fin.sum_univ_one, Nat.cast_zero, zero_add, inv_one, one_smul]

end AffineSimplex

section DiameterEstimate

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma norm_linSimplexBarycenter_sub_vertex_le {n : ℕ} (σ : Fin (n + 1) → W) (i : Fin (n + 1))
    {s : ℝ} (hs : ∀ j, ‖σ j - σ i‖ ≤ s) :
    ‖linSimplexBarycenter σ - σ i‖ ≤ (n : ℝ) / ((n : ℝ) + 1) * s := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hsub : linSimplexBarycenter σ - σ i = linSimplexBarycenter (fun j => σ j - σ i) := by
    simpa [linSimplexBarycenter, vsub_eq_sub] using
      Finset.centroid_vsub_const (k := ℝ) (s := Finset.univ) (p := σ) (p₀ := σ i)
        ⟨0, Finset.mem_univ 0⟩
  rw [hsub, linSimplexBarycenter_eq_avg, norm_smul, norm_inv, Real.norm_of_nonneg hpos.le]
  have hbound : ‖∑ j, (σ j - σ i)‖ ≤ (n : ℝ) * s := by
    calc ‖∑ j, (σ j - σ i)‖ ≤ ∑ j, ‖σ j - σ i‖ := norm_sum_le _ _
      _ = ∑ j ∈ Finset.univ.erase i, ‖σ j - σ i‖ :=
          (Finset.sum_erase (Finset.univ : Finset (Fin (n + 1)))
            (show ‖σ i - σ i‖ = 0 by simp)).symm
      _ ≤ (Finset.univ.erase i).card • s := Finset.sum_le_card_nsmul _ _ _ (fun j _ => hs j)
      _ = (n : ℝ) * s := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
          simp [nsmul_eq_mul]
  rw [show (n : ℝ) / ((n : ℝ) + 1) * s = ((n : ℝ) + 1)⁻¹ * ((n : ℝ) * s) by
    rw [div_eq_inv_mul]; ring]
  exact mul_le_mul_of_nonneg_left hbound (by positivity)

lemma dist_linSimplexBarycenter_le_of_mem {n : ℕ} (σ : Fin (n + 1) → W) {x : W}
    (hx : x ∈ convexHull ℝ (Set.range σ)) :
    ‖linSimplexBarycenter σ - x‖ ≤ (n : ℝ) / ((n : ℝ) + 1) * Metric.diam (Set.range σ) := by
  have hverts : Set.range σ ⊆
      Metric.closedBall (linSimplexBarycenter σ)
        (((n : ℝ) / ((n : ℝ) + 1)) * Metric.diam (Set.range σ)) := by
    rintro _ ⟨i, rfl⟩
    rw [Metric.mem_closedBall, dist_comm, dist_eq_norm]
    refine norm_linSimplexBarycenter_sub_vertex_le σ i (s := Metric.diam (Set.range σ))
      (fun j => ?_)
    rw [← dist_eq_norm]
    exact Metric.dist_le_diam_of_mem (Set.finite_range σ).isBounded ⟨j, rfl⟩ ⟨i, rfl⟩
  have hx' := convexHull_min hverts (convex_closedBall _ _) hx
  rwa [Metric.mem_closedBall, dist_comm, dist_eq_norm] at hx'

omit [NormedSpace ℝ W] in
lemma diam_vecCons_le {k : ℕ} (b : W) (w : Fin (k + 1) → W) {D : ℝ} (hD : 0 ≤ D)
    (hw : Metric.diam (Set.range w) ≤ D) (hb : ∀ i, dist b (w i) ≤ D) :
    Metric.diam (Set.range (vecCons b w)) ≤ D := by
  refine Metric.diam_le_of_forall_dist_le hD ?_
  rintro _ ⟨jx, rfl⟩ _ ⟨jy, rfl⟩
  refine Fin.cases ?_ (fun ix => ?_) jx <;> refine Fin.cases ?_ (fun iy => ?_) jy <;>
    simp only [cons_val_zero, cons_val_succ]
  · simpa using hD
  · exact hb iy
  · rw [dist_comm]; exact hb ix
  · exact le_trans (Metric.dist_le_diam_of_mem (Set.finite_range w).isBounded
      ⟨ix, rfl⟩ ⟨iy, rfl⟩) hw

end DiameterEstimate

end AlgebraicTopology
