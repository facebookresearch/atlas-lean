/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.Analysis.Normed.Module.Convex

/-!
# Centroid bounds for nested finite faces

This module proves coefficient-free metric estimates for centroids of finite
nested vertex sets in a real normed vector space.  It is independent of any
particular subdivision, simplicial-set, or chain-complex construction.
-/

@[expose] public section

open scoped BigOperators
open Set

noncomputable section

namespace AlgebraicTopology

universe u v

variable {ι : Type u} {V : Type v}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]

private lemma centroid_eq_inv_card_smul_sum
    {S : Finset ι} (hS : S.Nonempty) (v : ι → V) :
    S.centroid ℝ v = (S.card : ℝ)⁻¹ • ∑ i ∈ S, v i := by
  rw [Finset.centroid_def,
    Finset.affineCombination_eq_linear_combination]
  · simp [Finset.centroidWeights_apply, Finset.smul_sum]
  · exact S.sum_centroidWeights_eq_one_of_nonempty ℝ hS

private lemma centroid_mem_convexHull_image_of_subset
    {S T : Finset ι} (hS : S.Nonempty) (hST : S ⊆ T) (v : ι → V) :
    S.centroid ℝ v ∈ convexHull ℝ (v '' (T : Set ι)) := by
  rw [Finset.centroid_eq_centerMass S hS v]
  apply S.centerMass_mem_convexHull
  · intro i hi
    simp [Finset.centroidWeights_apply]
  · rw [S.sum_centroidWeights_eq_one_of_nonempty ℝ hS]
    norm_num
  · intro i hi
    exact ⟨i, hST hi, rfl⟩

private lemma centroid_subset_decomposition
    [DecidableEq ι] {S T : Finset ι} (hS : S.Nonempty) (hST : S ⊆ T)
    (hne : S ≠ T) (v : ι → V) :
    T.centroid ℝ v =
      ((S.card : ℝ) / (T.card : ℝ)) • S.centroid ℝ v +
        (((T \ S).card : ℝ) / (T.card : ℝ)) •
          (T \ S).centroid ℝ v := by
  classical
  have hT : T.Nonempty := hS.mono hST
  have hU : (T \ S).Nonempty := by
    rw [Finset.sdiff_nonempty]
    exact fun hTS ↦ hne (Finset.Subset.antisymm hST hTS)
  have hs0 : (S.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hS).ne'
  have ht0 : (T.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hT).ne'
  have hu0 : ((T \ S).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hU).ne'
  have hdisj : Disjoint S (T \ S) := Finset.disjoint_sdiff
  have hunion : S ∪ (T \ S) = T := Finset.union_sdiff_of_subset hST
  have hsum : (∑ i ∈ T, v i) =
      (∑ i ∈ S, v i) + ∑ i ∈ T \ S, v i := by
    calc
      (∑ i ∈ T, v i) = ∑ i ∈ S ∪ (T \ S), v i := by
        rw [hunion]
      _ = (∑ i ∈ S, v i) + ∑ i ∈ T \ S, v i := by
        rw [Finset.sum_union hdisj]
  have hscoef :
      ((S.card : ℝ) / (T.card : ℝ)) * (S.card : ℝ)⁻¹ =
        (T.card : ℝ)⁻¹ := by
    field_simp [hs0, ht0]
  have hucoef :
      (((T \ S).card : ℝ) / (T.card : ℝ)) *
          ((T \ S).card : ℝ)⁻¹ = (T.card : ℝ)⁻¹ := by
    field_simp [hu0, ht0]
  rw [centroid_eq_inv_card_smul_sum hT,
    centroid_eq_inv_card_smul_sum hS,
    centroid_eq_inv_card_smul_sum hU, hsum]
  simp only [smul_smul, hscoef, hucoef, smul_add]

/-- If `S` is a nonempty subset of `T`, the displacement between their
centroids is controlled by the fraction of vertices of `T` outside `S` and
the diameter of the vertices of `T`. -/
theorem dist_faceBarycenter_le
    {S T : Finset ι} (hS : S.Nonempty) (hST : S ⊆ T)
    (v : ι → V) :
    dist (S.centroid ℝ v) (T.centroid ℝ v) ≤
      (1 - (S.card : ℝ) / (T.card : ℝ)) *
        Metric.diam (v '' (T : Set ι)) := by
  classical
  have hT : T.Nonempty := hS.mono hST
  by_cases heq : S = T
  · subst T
    have hs0 : (S.card : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.card_pos.mpr hS).ne'
    simp [hs0]
  · have hU : (T \ S).Nonempty := by
      rw [Finset.sdiff_nonempty]
      exact fun hTS ↦ heq (Finset.Subset.antisymm hST hTS)
    have htpos : (0 : ℝ) < T.card := by
      exact_mod_cast Finset.card_pos.mpr hT
    have ht0 : (T.card : ℝ) ≠ 0 := htpos.ne'
    have hcard : S.card + (T \ S).card = T.card := by
      have hle : S.card ≤ T.card := Finset.card_le_card hST
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hST]
      omega
    have hcardR :
        (S.card : ℝ) + ((T \ S).card : ℝ) = T.card := by
      exact_mod_cast hcard
    have hcoef :
        ((T \ S).card : ℝ) / (T.card : ℝ) =
          1 - (S.card : ℝ) / (T.card : ℝ) := by
      field_simp [ht0]
      linarith [hcardR]
    have hratio_le :
        (S.card : ℝ) / (T.card : ℝ) ≤ 1 := by
      rw [div_le_iff₀ htpos]
      norm_num
      exact_mod_cast Finset.card_le_card hST
    have hcoef_nonneg :
        0 ≤ 1 - (S.card : ℝ) / (T.card : ℝ) :=
      sub_nonneg.mpr hratio_le
    have hdecomp := centroid_subset_decomposition hS hST heq v
    have hdiff :
        S.centroid ℝ v - T.centroid ℝ v =
          (1 - (S.card : ℝ) / (T.card : ℝ)) •
            (S.centroid ℝ v - (T \ S).centroid ℝ v) := by
      rw [hdecomp, hcoef]
      module
    have hSmem : S.centroid ℝ v ∈
        convexHull ℝ (v '' (T : Set ι)) :=
      centroid_mem_convexHull_image_of_subset hS hST v
    have hUmem : (T \ S).centroid ℝ v ∈
        convexHull ℝ (v '' (T : Set ι)) :=
      centroid_mem_convexHull_image_of_subset hU Finset.sdiff_subset v
    have hbounded : Bornology.IsBounded (v '' (T : Set ι)) :=
      (T.finite_toSet.image v).isBounded
    have hdist :
        dist (S.centroid ℝ v) ((T \ S).centroid ℝ v) ≤
          Metric.diam (v '' (T : Set ι)) := by
      simpa only [convexHull_diam] using
        Metric.dist_le_diam_of_mem
          (isBounded_convexHull.mpr hbounded) hSmem hUmem
    calc
      dist (S.centroid ℝ v) (T.centroid ℝ v) =
          ‖S.centroid ℝ v - T.centroid ℝ v‖ := dist_eq_norm _ _
      _ = ‖(1 - (S.card : ℝ) / (T.card : ℝ)) •
          (S.centroid ℝ v - (T \ S).centroid ℝ v)‖ := by
        rw [hdiff]
      _ = (1 - (S.card : ℝ) / (T.card : ℝ)) *
          ‖S.centroid ℝ v - (T \ S).centroid ℝ v‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hcoef_nonneg]
      _ = (1 - (S.card : ℝ) / (T.card : ℝ)) *
          dist (S.centroid ℝ v) ((T \ S).centroid ℝ v) := by
        rw [dist_eq_norm]
      _ ≤ (1 - (S.card : ℝ) / (T.card : ℝ)) *
          Metric.diam (v '' (T : Set ι)) :=
        mul_le_mul_of_nonneg_left hdist hcoef_nonneg

/-- The diameter of the centroids of a monotone chain of nonempty finite
faces is controlled by the intrinsic cardinal factor of its maximal face. -/
theorem diam_faceBarycenters_chain_le
    {d : ℕ} (faces : Fin (d + 1) → Finset ι)
    (hne : ∀ j, (faces j).Nonempty)
    (hchain : Monotone faces) (v : ι → V) :
    Metric.diam (Set.range (fun j ↦ (faces j).centroid ℝ v)) ≤
      (1 - 1 / ((faces (Fin.last d)).card : ℝ)) *
        Metric.diam (v '' (faces (Fin.last d) : Set ι)) := by
  let M := faces (Fin.last d)
  have hmpos : (0 : ℝ) < M.card := by
    exact_mod_cast Finset.card_pos.mpr (hne (Fin.last d))
  have hfactor_nonneg : 0 ≤ 1 - 1 / (M.card : ℝ) := by
    have hmone : (1 : ℝ) ≤ M.card := by
      exact_mod_cast Finset.one_le_card.mpr (hne (Fin.last d))
    have hone : 1 / (M.card : ℝ) ≤ 1 := by
      rw [div_le_iff₀ hmpos]
      simpa using hmone
    linarith
  have hdiam_nonneg : 0 ≤ Metric.diam (v '' (M : Set ι)) :=
    Metric.diam_nonneg
  apply Metric.diam_le_of_forall_dist_le
    (mul_nonneg hfactor_nonneg hdiam_nonneg)
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  have hpair : ∀ {i j : Fin (d + 1)}, i ≤ j →
      dist ((faces i).centroid ℝ v) ((faces j).centroid ℝ v) ≤
        (1 - 1 / (M.card : ℝ)) *
          Metric.diam (v '' (M : Set ι)) := by
    intro i j hij
    have hijFaces : faces i ⊆ faces j := hchain hij
    have hjM : faces j ⊆ M := hchain (Fin.le_last j)
    have hsone : (1 : ℝ) ≤ (faces i).card := by
      exact_mod_cast Finset.one_le_card.mpr (hne i)
    have htpos : (0 : ℝ) < (faces j).card := by
      exact_mod_cast Finset.card_pos.mpr (hne j)
    have htm : ((faces j).card : ℝ) ≤ M.card := by
      exact_mod_cast Finset.card_le_card hjM
    have hfrac :
        1 / (M.card : ℝ) ≤
          ((faces i).card : ℝ) / (faces j).card := by
      rw [div_le_div_iff₀ hmpos htpos]
      nlinarith [hsone, htm, le_of_lt hmpos]
    have hcoef :
        1 - ((faces i).card : ℝ) / (faces j).card ≤
          1 - 1 / (M.card : ℝ) :=
      sub_le_sub_left hfrac 1
    have hdiam :
        Metric.diam (v '' (faces j : Set ι)) ≤
          Metric.diam (v '' (M : Set ι)) := by
      apply Metric.diam_mono (Set.image_mono hjM)
      exact (M.finite_toSet.image v).isBounded
    calc
      dist ((faces i).centroid ℝ v) ((faces j).centroid ℝ v) ≤
          (1 - ((faces i).card : ℝ) / (faces j).card) *
            Metric.diam (v '' (faces j : Set ι)) :=
        dist_faceBarycenter_le (hne i) hijFaces v
      _ ≤ (1 - 1 / (M.card : ℝ)) *
          Metric.diam (v '' (M : Set ι)) :=
        mul_le_mul hcoef hdiam Metric.diam_nonneg hfactor_nonneg
  rcases le_total i j with hij | hji
  · exact hpair hij
  · rw [dist_comm]
    exact hpair hji

/-- If every face in the chain lies in an `N`-simplex-sized maximal face,
the intrinsic factor is at most `N / (N + 1)`. -/
theorem diam_faceBarycenters_chain_le_of_card_le
    {d N : ℕ} (faces : Fin (d + 1) → Finset ι)
    (hne : ∀ j, (faces j).Nonempty)
    (hchain : Monotone faces)
    (hcard : (faces (Fin.last d)).card ≤ N + 1)
    (v : ι → V) :
    Metric.diam (Set.range (fun j ↦ (faces j).centroid ℝ v)) ≤
      (N : ℝ) / (N + 1) *
        Metric.diam (v '' (faces (Fin.last d) : Set ι)) := by
  let M := faces (Fin.last d)
  have hmpos : (0 : ℝ) < M.card := by
    exact_mod_cast Finset.card_pos.mpr (hne (Fin.last d))
  have hnpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hmle : (M.card : ℝ) ≤ (N : ℝ) + 1 := by
    exact_mod_cast hcard
  have hinv : 1 / ((N : ℝ) + 1) ≤ 1 / (M.card : ℝ) := by
    rw [div_le_div_iff₀ hnpos hmpos]
    simpa using hmle
  have hfactor :
      1 - 1 / (M.card : ℝ) ≤ (N : ℝ) / (N + 1) := by
    have heq :
        (N : ℝ) / (N + 1) = 1 - 1 / ((N : ℝ) + 1) := by
      field_simp
      ring
    rw [heq]
    exact sub_le_sub_left hinv 1
  calc
    Metric.diam (Set.range (fun j ↦ (faces j).centroid ℝ v)) ≤
        (1 - 1 / (M.card : ℝ)) *
          Metric.diam (v '' (M : Set ι)) :=
      diam_faceBarycenters_chain_le faces hne hchain v
    _ ≤ (N : ℝ) / (N + 1) *
        Metric.diam (v '' (M : Set ι)) :=
      mul_le_mul_of_nonneg_right hfactor Metric.diam_nonneg

end AlgebraicTopology
