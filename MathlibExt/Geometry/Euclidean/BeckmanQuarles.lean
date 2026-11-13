/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Geometry.Euclidean.Basic
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

open InnerProductSpace

/-- Two vectors in a 1-dimensional orthogonal complement with equal norm
    are equal or negations. -/
private theorem bq_eq_or_eq_neg_of_mem_orthogonal_of_finrank_one
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (K : Submodule ℝ V)
    (hK : Module.finrank ℝ Kᗮ = 1)
    (w w' : V) (hw : w ∈ Kᗮ) (hw' : w' ∈ Kᗮ) (hnorm : ‖w‖ = ‖w'‖) :
    w' = w ∨ w' = -w := by
  by_cases hw0 : w = 0
  · subst hw0
    rw [norm_zero] at hnorm
    have hw'0 : w' = 0 := norm_eq_zero.mp hnorm.symm
    simp [hw'0]
  · have hspan : ℝ ∙ (⟨w, hw⟩ : Kᗮ) = ⊤ :=
      (finrank_eq_one_iff_of_nonzero (⟨w, hw⟩ : Kᗮ) (by simpa using hw0)).mp hK
    have hmem : (⟨w', hw'⟩ : Kᗮ) ∈ ℝ ∙ (⟨w, hw⟩ : Kᗮ) := by rw [hspan]; trivial
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
    have hweq : w' = a • w := by
      have h := congrArg Subtype.val ha
      simpa using h.symm
    have h2 : ‖w'‖ = |a| * ‖w‖ := by
      conv_lhs => rw [hweq]
      rw [norm_smul, Real.norm_eq_abs]
    have hnorma : |a| * ‖w‖ = ‖w‖ := by rw [← h2]; exact hnorm.symm
    have hne : ‖w‖ ≠ 0 := fun h => hw0 (norm_eq_zero.mp h)
    have hne0 : (0 : ℝ) ≠ ‖w‖ := fun h => hne h.symm
    have hpos : 0 < ‖w‖ := lt_of_le_of_ne' (norm_nonneg w) hne
    have hnorma' : |a| * ‖w‖ = 1 * ‖w‖ := by rw [one_mul]; exact hnorma
    have habs : |a| = 1 := mul_right_cancel₀ (ne_of_gt hpos) hnorma'
    rcases eq_or_eq_neg_of_abs_eq habs with rfl | rfl
    · left; rw [hweq, one_smul]
    · right; rw [hweq, neg_smul, one_smul]

/-- Circle–circle intersection distance in the plane. -/
private theorem bq_planar_kite_dichotomy
    (p q z z' : EuclideanSpace ℝ (Fin 2)) (hpq : p ≠ q)
    (h1 : dist z p = dist z' p) (h2 : dist z q = dist z' q) :
    z = z' ∨ dist z z' ^ 2
      = 4 * dist z p ^ 2
        - (dist z p ^ 2 - dist z q ^ 2 + dist p q ^ 2) ^ 2 / dist p q ^ 2 := by
  have hs : (0 : ℝ) < dist p q := dist_pos.mpr hpq
  have d3 : dist p q = ‖q - p‖ := by rw [dist_comm, dist_eq_norm]
  have hSpos : (0 : ℝ) < ‖q - p‖ := d3 ▸ hs
  have hS2 : (0 : ℝ) < ‖q - p‖ ^ 2 := pow_pos hSpos 2
  have hS2ne : ‖q - p‖ ^ 2 ≠ 0 := ne_of_gt hS2
  have hene : q - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hpq)
  -- polarization constant
  set α : ℝ := (‖z - p‖ ^ 2 - ‖z - q‖ ^ 2 + ‖q - p‖ ^ 2) / 2 with hα
  set c : ℝ := α / ‖q - p‖ ^ 2 with hc_def
  have hcS : c * ‖q - p‖ ^ 2 = α := div_mul_cancel₀ α hS2ne
  have hpol : ⟪z - p, q - p⟫_ℝ = α := by
    have hexp := norm_sub_sq_real (z - p) (q - p)
    have hqe : (z - p) - (q - p) = z - q := by abel
    rw [hqe] at hexp
    linarith
  have e1 : ‖z' - p‖ = ‖z - p‖ := by
    have g : dist z' p = dist z p := h1.symm
    rwa [dist_eq_norm, dist_eq_norm] at g
  have e2 : ‖z' - q‖ = ‖z - q‖ := by
    have g : dist z' q = dist z q := h2.symm
    rwa [dist_eq_norm, dist_eq_norm] at g
  have hpol' : ⟪z' - p, q - p⟫_ℝ = α := by
    have hexp := norm_sub_sq_real (z' - p) (q - p)
    have hqe : (z' - p) - (q - p) = z' - q := by abel
    rw [hqe, e1, e2] at hexp
    linarith
  -- orthogonal residuals
  have horth : ⟪q - p, (z - p) - c • (q - p)⟫_ℝ = 0 := by
    rw [inner_sub_right, real_inner_comm (z - p) (q - p), hpol,
      real_inner_smul_right, real_inner_self_eq_norm_sq, hcS, sub_self]
  have horth' : ⟪q - p, (z' - p) - c • (q - p)⟫_ℝ = 0 := by
    rw [inner_sub_right, real_inner_comm (z' - p) (q - p), hpol',
      real_inner_smul_right, real_inner_self_eq_norm_sq, hcS, sub_self]
  have hmem : (z - p) - c • (q - p) ∈ (ℝ ∙ (q - p))ᗮ := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact horth
  have hmem' : (z' - p) - c • (q - p) ∈ (ℝ ∙ (q - p))ᗮ := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact horth'
  -- equal norms
  have hI : ⟪z - p, c • (q - p)⟫_ℝ = c * α := by
    rw [real_inner_smul_right, hpol]
  have hI' : ⟪z' - p, c • (q - p)⟫_ℝ = c * α := by
    rw [real_inner_smul_right, hpol']
  have hN : ‖c • (q - p)‖ ^ 2 = c * α := by
    have hg : ‖c • (q - p)‖ ^ 2 = c ^ 2 * ‖q - p‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [hg]
    calc c ^ 2 * ‖q - p‖ ^ 2 = c * (c * ‖q - p‖ ^ 2) := by ring
      _ = c * α := by rw [hcS]
  have hnorm2 : ‖(z - p) - c • (q - p)‖ ^ 2
      = ‖(z' - p) - c • (q - p)‖ ^ 2 := by
    have g1 := norm_sub_sq_real (z - p) (c • (q - p))
    have g2 := norm_sub_sq_real (z' - p) (c • (q - p))
    rw [hI, hN] at g1
    rw [hI', hN, e1] at g2
    linarith
  have hnorm_eq : ‖(z - p) - c • (q - p)‖ = ‖(z' - p) - c • (q - p)‖ := by
    have hnn : (0 : ℝ) ≤ ‖(z - p) - c • (q - p)‖ := norm_nonneg _
    have hnn2 : (0 : ℝ) ≤ ‖(z' - p) - c • (q - p)‖ := norm_nonneg _
    exact (pow_left_inj₀ hnn hnn2 two_ne_zero).mp hnorm2
  -- rank one, so the residuals agree up to sign
  have hrank : Module.finrank ℝ (ℝ ∙ (q - p))ᗮ = 1 := by
    have h1 := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ (q - p))
    rw [finrank_span_singleton hene, finrank_euclideanSpace_fin] at h1
    omega
  rcases bq_eq_or_eq_neg_of_mem_orthogonal_of_finrank_one (ℝ ∙ (q - p)) hrank
    _ _ hmem hmem' hnorm_eq with h | h
  · left
    have heq : (z' - p) - c • (q - p) = (z - p) - c • (q - p) := h
    have hsub : z' - p = z - p := by
      have hcc := congrArg (· + c • (q - p)) heq
      simpa using hcc
    have hzz : z' = z := by
      have hcc := congrArg (· + p) hsub
      simpa using hcc
    exact hzz.symm
  · right
    have hdiff : z - z' = (2 : ℝ) • ((z - p) - c • (q - p)) := by
      have hrr : z - z'
          = ((z - p) - c • (q - p)) - ((z' - p) - c • (q - p)) := by abel
      rw [hrr, h, two_smul]
      abel
    have hdist2 : dist z z' ^ 2 = 4 * ‖(z - p) - c • (q - p)‖ ^ 2 := by
      rw [dist_eq_norm, hdiff, norm_smul, Real.norm_eq_abs]
      rw [show |(2 : ℝ)| = 2 from by norm_num]
      ring
    have hw2 : ‖(z - p) - c • (q - p)‖ ^ 2
        = ‖z - p‖ ^ 2 - α ^ 2 / ‖q - p‖ ^ 2 := by
      have g1 := norm_sub_sq_real (z - p) (c • (q - p))
      rw [hI, hN] at g1
      have hc : c * α = α ^ 2 / ‖q - p‖ ^ 2 := by rw [hc_def]; ring
      rw [hc] at g1
      linarith
    have d1 : dist z p = ‖z - p‖ := dist_eq_norm _ _
    have d2 : dist z q = ‖z - q‖ := dist_eq_norm _ _
    have hX : (‖z - p‖ ^ 2 - ‖z - q‖ ^ 2 + ‖q - p‖ ^ 2) = 2 * α := by
      rw [hα]; ring
    rw [hdist2, hw2, d1, d2, d3, hX]
    ring

/-- Vertices of a regular simplex give linearly independent differences. -/
private theorem bq_linearIndependent_sub_of_pairwise_dist_eq
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {m : ℕ} {s : ℝ} (hs : 0 < s) (v : Fin (m + 1) → V)
    (hdist : ∀ i j : Fin (m + 1), i ≠ j → dist (v i) (v j) = s) :
    LinearIndependent ℝ (fun k : Fin m => v (Fin.succ k) - v 0) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg k
  have hnorm : ∀ k : Fin m, ‖v (Fin.succ k) - v 0‖ = s := by
    intro k
    rw [← dist_eq_norm]
    exact hdist _ _ (Fin.succ_ne_zero k)
  have hdiag : ∀ k : Fin m,
      ⟪v (Fin.succ k) - v 0, v (Fin.succ k) - v 0⟫_ℝ = s ^ 2 := by
    intro k
    rw [real_inner_self_eq_norm_sq, hnorm k]
  have hinner : ∀ k l : Fin m, k ≠ l →
      ⟪v (Fin.succ k) - v 0, v (Fin.succ l) - v 0⟫_ℝ = s ^ 2 / 2 := by
    intro k l hkl
    have h1 : ‖(v (Fin.succ k) - v 0) - (v (Fin.succ l) - v 0)‖ = s := by
      have he : (v (Fin.succ k) - v 0) - (v (Fin.succ l) - v 0)
        = v (Fin.succ k) - v (Fin.succ l) := by abel
      rw [he, ← dist_eq_norm]
      apply hdist
      intro hcon
      exact hkl (Fin.succ_inj.mp hcon)
    have hexpand := norm_sub_sq_real (v (Fin.succ k) - v 0) (v (Fin.succ l) - v 0)
    rw [h1, hnorm k, hnorm l] at hexpand
    linarith [hexpand]
  have hsum0 : ‖∑ k : Fin m, g k • (v (Fin.succ k) - v 0)‖ ^ 2 = 0 := by
    rw [hg]; simp
  rw [← real_inner_self_eq_norm_sq] at hsum0
  have hexp : ⟪∑ k : Fin m, g k • (v (Fin.succ k) - v 0),
      ∑ l : Fin m, g l • (v (Fin.succ l) - v 0)⟫_ℝ
      = ∑ k : Fin m, ∑ l : Fin m, g k * g l * (if k = l then s ^ 2 else s ^ 2 / 2) := by
    rw [inner_sum]
    apply Finset.sum_congr rfl; intro k _
    rw [sum_inner]
    apply Finset.sum_congr rfl; intro l _
    rw [real_inner_smul_left, real_inner_smul_right]
    by_cases hkl : k = l
    · subst hkl; simp only [hdiag k, ite_true]; ring
    · rw [hinner l k (fun h => hkl h.symm), ite_eq_right hkl]; ring
  rw [hexp] at hsum0
  have hclosed : (∑ k : Fin m, ∑ l : Fin m, g k * g l * (if k = l then s ^ 2 else s ^ 2 / 2))
      = (s ^ 2 / 2) * ((∑ k : Fin m, (g k) ^ 2) + (∑ k : Fin m, g k) ^ 2) := by
    have hsplit : ∀ k : Fin m, (∑ l : Fin m, g k * g l * (if k = l then s ^ 2 else s ^ 2 / 2))
        = g k * g k * s ^ 2 + (s ^ 2 / 2) * (g k * ((∑ l : Fin m, g l) - g k)) := by
      intro k
      conv_lhs => rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
      congr 1
      · simp
      · have hterm : (∑ x ∈ Finset.univ.erase k,
              g k * g x * (if k = x then s ^ 2 else s ^ 2 / 2))
            = ∑ x ∈ Finset.univ.erase k, (s ^ 2 / 2) * (g k * g x) := by
          apply Finset.sum_congr rfl; intro l hl
          have hkl : k ≠ l := Ne.symm (Finset.mem_erase.mp hl).1
          rw [ite_eq_right hkl]; ring
        rw [hterm, ← Finset.mul_sum, ← Finset.mul_sum]
        congr 1
        have herase : (∑ x ∈ Finset.univ.erase k, g x) = (∑ l : Fin m, g l) - g k := by
          have h := Finset.add_sum_erase Finset.univ g (Finset.mem_univ k)
          linarith [h]
        rw [herase]
    simp_rw [hsplit, Finset.sum_add_distrib]
    have hA : (∑ k : Fin m, g k * g k * s ^ 2) = s ^ 2 * (∑ k : Fin m, (g k) ^ 2) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
    have hB : (∑ k : Fin m, (s ^ 2 / 2) * (g k * ((∑ l : Fin m, g l) - g k)))
        = (s ^ 2 / 2) * ((∑ k : Fin m, g k) ^ 2 - (∑ k : Fin m, (g k) ^ 2)) := by
      rw [← Finset.mul_sum]
      congr 1
      simp_rw [mul_sub, Finset.sum_sub_distrib]
      rw [← Finset.sum_mul]
      have hC : (∑ k : Fin m, g k * g k) = ∑ k : Fin m, (g k) ^ 2 := by
        apply Finset.sum_congr rfl; intro k _; ring
      rw [hC, sq]
    rw [hA, hB]; ring
  rw [hclosed] at hsum0
  have hs2 : (0 : ℝ) < s ^ 2 / 2 := by positivity
  have hzero : (∑ k : Fin m, (g k) ^ 2) + (∑ k : Fin m, g k) ^ 2 = 0 := by
    rcases mul_eq_zero.mp hsum0 with h | h
    · linarith [hs2.ne']
    · exact h
  have hsq : ∑ k : Fin m, (g k) ^ 2 = 0 := by
    have h1 : (0 : ℝ) ≤ ∑ k : Fin m, (g k) ^ 2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have h2 : (0 : ℝ) ≤ (∑ k : Fin m, g k) ^ 2 := sq_nonneg _
    linarith
  have hkk := Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => sq_nonneg (g i)) |>.mp hsq k (Finset.mem_univ k)
  simpa using hkk

/-- Centroid inner products: differences from a fixed vertex. -/
private theorem bq_centroid_inner {m : ℕ} {s : ℝ} (_hs : 0 < s)
    (v : Fin (m + 2) → EuclideanSpace ℝ (Fin (m + 2)))
    (hdist : ∀ i j, i ≠ j → dist (v i) (v j) = s)
    (i j l : Fin (m + 2)) (hj : j ≠ i) (hl : l ≠ i) :
    ⟪v i - v j, v i - v l⟫_ℝ = if j = l then s ^ 2 else s ^ 2 / 2 := by
  by_cases hjl : j = l
  · subst hjl
    rw [ite_eq_left rfl, real_inner_self_eq_norm_sq, ← dist_eq_norm]
    rw [hdist i j (Ne.symm hj)]
  · rw [ite_eq_right hjl]
    have hnorm_j : ‖v i - v j‖ = s := by
      rw [← dist_eq_norm]
      exact hdist i j (Ne.symm hj)
    have hnorm_l : ‖v i - v l‖ = s := by
      rw [← dist_eq_norm]
      exact hdist i l (Ne.symm hl)
    have hdiff : ‖(v i - v j) - (v i - v l)‖ = s := by
      have he : (v i - v j) - (v i - v l) = v l - v j := by abel
      rw [he, ← dist_eq_norm]
      exact hdist l j (fun h => hjl h.symm)
    have hexpand := norm_sub_sq_real (v i - v j) (v i - v l)
    rw [hdiff, hnorm_j, hnorm_l] at hexpand
    linarith [hexpand]

/-- Double sum over an erased Fin set with diagonal/off-diagonal values. -/
private theorem bq_erased_double_sum (m : ℕ) (s : ℝ) (i : Fin (m + 2)) :
    ∑ _j ∈ Finset.univ.erase i, ∑ _l ∈ Finset.univ.erase i,
        (if _j = _l then s ^ 2 else s ^ 2 / 2)
      = s ^ 2 * (m + 1) * (m + 2) / 2 := by
  have hcard : (Finset.univ.erase i).card = m + 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp [Fintype.card_fin]
  have hinner : ∀ j ∈ Finset.univ.erase i,
      (∑ _l ∈ Finset.univ.erase i, (if j = _l then s ^ 2 else s ^ 2 / 2))
        = s ^ 2 * (m + 2) / 2 := by
    intro j hj
    have hsplit := Finset.add_sum_erase (Finset.univ.erase i)
      (fun _l => if j = _l then s ^ 2 else s ^ 2 / 2) hj
    rw [← hsplit]
    simp only [ite_true]
    have herase : ((Finset.univ.erase i).erase j).card = m := by
      rw [Finset.card_erase_of_mem hj, hcard, Nat.add_sub_cancel]
    have hoff : ∑ _x ∈ (Finset.univ.erase i).erase j,
        (if j = _x then s ^ 2 else s ^ 2 / 2)
        = ∑ _x ∈ (Finset.univ.erase i).erase j, (s ^ 2 / 2) := by
      apply Finset.sum_congr rfl
      intro l hl
      have hne : j ≠ l := Ne.symm (Finset.mem_erase.mp hl).1
      rw [ite_eq_right hne]
    rw [hoff, Finset.sum_const, herase, nsmul_eq_mul]
    ring
  calc ∑ _j ∈ Finset.univ.erase i, ∑ _l ∈ Finset.univ.erase i,
          (if _j = _l then s ^ 2 else s ^ 2 / 2)
        = ∑ _j ∈ Finset.univ.erase i, (s ^ 2 * (m + 2) / 2) :=
        Finset.sum_congr rfl hinner
      _ = s ^ 2 * (m + 1) * (m + 2) / 2 := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul]
        push_cast
        ring

/-- Centroid decomposition: deviation from mean as scaled sum of differences. -/
private theorem bq_centroid_decomp (m : ℕ)
    (v : Fin (m + 2) → EuclideanSpace ℝ (Fin (m + 2)))
    (i : Fin (m + 2)) :
    v i - ((m : ℝ) + 2)⁻¹ • ∑ j, v j
      = ((m : ℝ) + 2)⁻¹ • ∑ j, (v i - v j) := by
  have hnR : ((m : ℝ) + 2) ≠ 0 := by positivity
  have hsum : ∑ j, (v i - v j)
      = (Fintype.card (Fin (m + 2))) • v i - ∑ j, v j := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ]
  have hcard : Fintype.card (Fin (m + 2)) = m + 2 := Fintype.card_fin _
  have hns : (Fintype.card (Fin (m + 2))) • v i
      = ((m : ℝ) + 2) • v i := by
    have e1 : (Fintype.card (Fin (m + 2))) • v i
        = ((Fintype.card (Fin (m + 2)) : ℕ) : ℝ) • v i :=
      (Nat.cast_smul_eq_nsmul (R := ℝ) _ _).symm
    rw [e1, hcard]
    push_cast
    rfl
  have hinv : ((m : ℝ) + 2)⁻¹ • (((m : ℝ) + 2) • v i) = v i :=
    inv_smul_smul₀ hnR (v i)
  rw [hsum, hns, smul_sub, hinv]

/-- Centroid distance of a regular simplex. -/
private theorem bq_centroid_dist {m : ℕ} {s : ℝ} (hs : 0 < s)
    (v : Fin (m + 2) → EuclideanSpace ℝ (Fin (m + 2)))
    (hdist : ∀ i j, i ≠ j → dist (v i) (v j) = s)
    (i : Fin (m + 2)) :
    ‖v i - ((m : ℝ) + 2)⁻¹ • ∑ j, v j‖ ^ 2
      = s ^ 2 * ((m : ℝ) + 1) / (2 * ((m : ℝ) + 2)) := by
  have hnR : ((m : ℝ) + 2) ≠ 0 := by positivity
  have hdi : v i - v i = (0 : EuclideanSpace ℝ (Fin (m + 2))) := sub_self _
  have hdrop : ∑ j, (v i - v j)
      = ∑ j ∈ Finset.univ.erase i, (v i - v j) := by
    conv_lhs => rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    rw [hdi, zero_add]
  have hexp : ⟪∑ j ∈ Finset.univ.erase i, (v i - v j),
      ∑ l ∈ Finset.univ.erase i, (v i - v l)⟫_ℝ
      = ∑ j ∈ Finset.univ.erase i, ∑ l ∈ Finset.univ.erase i,
        (if j = l then s ^ 2 else s ^ 2 / 2) := by
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro j hj
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro l hl
    have hjm : j ≠ i := (Finset.mem_erase.mp hj).1
    have hlm : l ≠ i := (Finset.mem_erase.mp hl).1
    rw [bq_centroid_inner hs v hdist i j l hjm hlm]
  have hnorm2 : ‖∑ j, (v i - v j)‖ ^ 2
      = s ^ 2 * (m + 1) * (m + 2) / 2 := by
    rw [hdrop, ← real_inner_self_eq_norm_sq, hexp]
    exact bq_erased_double_sum m s i
  rw [bq_centroid_decomp m v i, norm_smul, Real.norm_eq_abs, mul_pow]
  rw [hnorm2, sq_abs]
  field_simp

/-- Apex dichotomy for a regular simplex. -/
private theorem bq_regular_simplex_apex_dichotomy {m : ℕ} {s : ℝ} (hs : 0 < s)
    (v : Fin (m + 2) → EuclideanSpace ℝ (Fin (m + 2)))
    (hdist : ∀ i j, i ≠ j → dist (v i) (v j) = s)
    (z z' : EuclideanSpace ℝ (Fin (m + 2))) (r : ℝ)
    (hz : ∀ i, dist z (v i) = r) (hz' : ∀ i, dist z' (v i) = r) :
    z = z' ∨ dist z z' ^ 2
      = 4 * r ^ 2 - 2 * s ^ 2 * ((m : ℝ) + 1) / ((m : ℝ) + 2) := by
  have hnR : ((m : ℝ) + 2) ≠ 0 := by positivity
  set g : EuclideanSpace ℝ (Fin (m + 2))
    := ((m : ℝ) + 2)⁻¹ • ∑ j, v j with hg
  have hg_norm2 : ∀ i, ‖v i - g‖ ^ 2
      = s ^ 2 * ((m : ℝ) + 1) / (2 * ((m : ℝ) + 2)) :=
    fun i => bq_centroid_dist hs v hdist i
  have hg_eq : ∀ a b, dist (v a) g = dist (v b) g := by
    intro a b
    rw [dist_eq_norm, dist_eq_norm]
    have ha := hg_norm2 a
    have hb := hg_norm2 b
    have hnn : (0 : ℝ) ≤ ‖v a - g‖ := norm_nonneg _
    have hnn2 : (0 : ℝ) ≤ ‖v b - g‖ := norm_nonneg _
    have heq : ‖v a - g‖ ^ 2 = ‖v b - g‖ ^ 2 := by rw [ha, hb]
    exact (pow_left_inj₀ hnn hnn2 two_ne_zero).mp heq
  -- direction space and its rank
  set bvec : Fin (m + 1) → EuclideanSpace ℝ (Fin (m + 2))
    := fun k => v (Fin.succ k) - v 0 with hbvec
  set K : Submodule ℝ (EuclideanSpace ℝ (Fin (m + 2)))
    := Submodule.span ℝ (Set.range bvec) with hK
  have hindep : LinearIndependent ℝ bvec :=
    bq_linearIndependent_sub_of_pairwise_dist_eq (m := m + 1) hs v hdist
  have hKrank : Module.finrank ℝ K = m + 1 := by
    rw [hK, finrank_span_eq_card hindep, Fintype.card_fin]
  have hErank : Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 2))) = m + 2 :=
    finrank_euclideanSpace_fin
  have horth_rank : Module.finrank ℝ Kᗮ = 1 := by
    have h := Submodule.finrank_add_finrank_orthogonal K
    omega
  -- each generator is orthogonal to z - g
  have hgen : ∀ k : Fin (m + 1),
      ⟪z - g, v (Fin.succ k) - v 0⟫_ℝ = 0 := by
    intro k
    have hc1 : dist (v 0) g = dist (v (Fin.succ k)) g := hg_eq 0 _
    have hc2 : dist (v 0) z = dist (v (Fin.succ k)) z := by
      rw [dist_comm (v 0) z, dist_comm (v (Fin.succ k)) z, hz 0, hz _]
    have hkite := EuclideanGeometry.inner_vsub_vsub_of_dist_eq_of_dist_eq
      hc1 hc2
    simp only [vsub_eq_sub] at hkite
    exact hkite
  have hgen' : ∀ k : Fin (m + 1),
      ⟪z' - g, v (Fin.succ k) - v 0⟫_ℝ = 0 := by
    intro k
    have hc1 : dist (v 0) g = dist (v (Fin.succ k)) g := hg_eq 0 _
    have hc2 : dist (v 0) z' = dist (v (Fin.succ k)) z' := by
      rw [dist_comm (v 0) z', dist_comm (v (Fin.succ k)) z', hz' 0, hz' _]
    have hkite := EuclideanGeometry.inner_vsub_vsub_of_dist_eq_of_dist_eq
      hc1 hc2
    simp only [vsub_eq_sub] at hkite
    exact hkite
  have hmem : z - g ∈ Kᗮ := by
    rw [Submodule.mem_orthogonal']
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact hgen k
    | zero => simp
    | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
    | smul a x _ hx => rw [inner_smul_right, hx, mul_zero]
  have hmem' : z' - g ∈ Kᗮ := by
    rw [Submodule.mem_orthogonal']
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact hgen' k
    | zero => simp
    | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
    | smul a x _ hx => rw [inner_smul_right, hx, mul_zero]
  -- g - v 0 lies in K
  have hgen_mem : ∀ j, v j - v 0 ∈ K := by
    intro j
    by_cases hj0 : j = 0
    · subst hj0
      simp [hK]
    · obtain ⟨k, hk⟩ := Fin.exists_succ_eq_of_ne_zero hj0
      have hkk : bvec k = v j - v 0 := by simp only [hbvec]; rw [hk]
      rw [← hkk]
      exact Submodule.subset_span ⟨k, rfl⟩
  have hgK : g - v 0 ∈ K := by
    have hsum : ∑ j, (v j - v 0) ∈ K :=
      Submodule.sum_mem K (fun j _ => hgen_mem j)
    have hdecomp : g - v 0 = ((m : ℝ) + 2)⁻¹ • ∑ j, (v j - v 0) := by
      have hsum2 : ∑ j, (v j - v 0)
          = ∑ j, v j - (Fintype.card (Fin (m + 2))) • v 0 := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ]
      have hcard : Fintype.card (Fin (m + 2)) = m + 2 := Fintype.card_fin _
      have e1 : (Fintype.card (Fin (m + 2))) • v 0
          = ((m : ℝ) + 2) • v 0 :=
        ((Nat.cast_smul_eq_nsmul (R := ℝ) _ _).symm.trans (by
          rw [hcard]
          push_cast
          rfl))
      have hinv : ((m : ℝ) + 2)⁻¹ • (((m : ℝ) + 2) • v 0) = v 0 :=
        inv_smul_smul₀ hnR (v 0)
      rw [hg, hsum2, e1, smul_sub, hinv]
    rw [hdecomp]
    exact Submodule.smul_mem K _ hsum
  -- Pythagoras for z - g
  have hR2 : ‖g - v 0‖ ^ 2
      = s ^ 2 * ((m : ℝ) + 1) / (2 * ((m : ℝ) + 2)) := by
    have h0 := hg_norm2 0
    rwa [norm_sub_rev] at h0
  have hzr : ‖z - v 0‖ = r := by
    rw [← dist_eq_norm]
    exact hz 0
  have hzorth : ⟪z - g, g - v 0⟫_ℝ = 0 :=
    Submodule.inner_left_of_mem_orthogonal hgK hmem
  have hzg2 : ‖z - g‖ ^ 2
      = r ^ 2 - s ^ 2 * ((m : ℝ) + 1) / (2 * ((m : ℝ) + 2)) := by
    have hdecomp : z - v 0 = (z - g) + (g - v 0) := by abel
    have hexp := norm_add_sq_real (z - g) (g - v 0)
    rw [hzorth, mul_zero, add_zero] at hexp
    rw [← hdecomp, hzr, hR2] at hexp
    linarith [hexp]
  have hz'orth : ⟪z' - g, g - v 0⟫_ℝ = 0 :=
    Submodule.inner_left_of_mem_orthogonal hgK hmem'
  have hzg2' : ‖z' - g‖ ^ 2
      = r ^ 2 - s ^ 2 * ((m : ℝ) + 1) / (2 * ((m : ℝ) + 2)) := by
    have hzr' : ‖z' - v 0‖ = r := by
      rw [← dist_eq_norm]
      exact hz' 0
    have hdecomp : z' - v 0 = (z' - g) + (g - v 0) := by abel
    have hexp := norm_add_sq_real (z' - g) (g - v 0)
    rw [hz'orth, mul_zero, add_zero] at hexp
    rw [← hdecomp, hzr', hR2] at hexp
    linarith [hexp]
  have hnorm_eq : ‖z' - g‖ = ‖z - g‖ := by
    have hnn : (0 : ℝ) ≤ ‖z - g‖ := norm_nonneg _
    have hnn2 : (0 : ℝ) ≤ ‖z' - g‖ := norm_nonneg _
    exact (pow_left_inj₀ hnn2 hnn two_ne_zero).mp (by rw [hzg2', hzg2])
  rcases bq_eq_or_eq_neg_of_mem_orthogonal_of_finrank_one K horth_rank
    (z - g) (z' - g) hmem hmem' hnorm_eq.symm with h | h
  · left
    have heq : z' - g = z - g := h
    have : z' = z := by
      have := congrArg (· + g) heq
      simpa using this
    exact this.symm
  · right
    have hdiff : z - z' = (2 : ℝ) • (z - g) := by
      have heq : z' - g = -(z - g) := h
      have hrr : z - z' = (z - g) - (z' - g) := by abel
      rw [hrr, heq, two_smul]
      abel
    have hdist2 : dist z z' ^ 2 = 4 * ‖z - g‖ ^ 2 := by
      rw [dist_eq_norm, hdiff, norm_smul, Real.norm_eq_abs]
      rw [show |(2 : ℝ)| = 2 from by norm_num]
      ring
    rw [hdist2, hzg2]
    field_simp
    ring

/-- Standard basis inner products. -/
private theorem bq_single_inner {n : ℕ} (i j : Fin n) :
    ⟪EuclideanSpace.single i (1 : ℝ),
      EuclideanSpace.single j (1 : ℝ)⟫_ℝ
      = if i = j then 1 else 0 :=
  orthonormal_iff_ite.mp EuclideanSpace.orthonormal_single i j

/-- Inner product of a basis vector with the all-ones vector. -/
private theorem bq_single_one_inner {n : ℕ} (i : Fin n) :
    ⟪EuclideanSpace.single i (1 : ℝ),
      ∑ j, EuclideanSpace.single j (1 : ℝ)⟫_ℝ = 1 := by
  rw [inner_sum]
  simp_rw [bq_single_inner]
  rw [Finset.sum_ite_eq]
  simp

/-- Squared norm of the all-ones vector. -/
private theorem bq_one_norm2 {n : ℕ} :
    ‖(∑ j, EuclideanSpace.single j (1 : ℝ) :
      EuclideanSpace ℝ (Fin n))‖ ^ 2 = (n : ℝ) := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  simp_rw [bq_single_one_inner]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one]

/-- Squared norm of a difference of distinct basis vectors. -/
private theorem bq_single_sub_norm2 {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    ‖EuclideanSpace.single i (1 : ℝ)
      - EuclideanSpace.single j (1 : ℝ)‖ ^ 2 = 2 := by
  have h1 : ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 := by simp
  have h2 : ‖EuclideanSpace.single j (1 : ℝ)‖ = 1 := by simp
  have hij2 : ⟪EuclideanSpace.single i (1 : ℝ),
      EuclideanSpace.single j (1 : ℝ)⟫_ℝ = 0 := by
    rw [bq_single_inner, ite_eq_right hij]
  have hexp := norm_sub_sq_real (EuclideanSpace.single i (1 : ℝ))
    (EuclideanSpace.single j (1 : ℝ))
  rw [hij2, h1, h2] at hexp
  norm_num at hexp
  exact hexp

/-- Squared norm of a centered basis vector. -/
private theorem bq_single_centered_norm2 {n : ℕ} (hn : (n : ℝ) ≠ 0)
    (i : Fin n) :
    ‖EuclideanSpace.single i (1 : ℝ) - (n : ℝ)⁻¹ • ∑ j : Fin n,
        EuclideanSpace.single j (1 : ℝ)‖ ^ 2
      = ((n : ℝ) - 1) / (n : ℝ) := by
  have h1 : ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 := by simp
  have hone : ⟪EuclideanSpace.single i (1 : ℝ),
      ∑ j : Fin n, EuclideanSpace.single j (1 : ℝ)⟫_ℝ = 1 :=
    bq_single_one_inner i
  have hnorm1 : ‖(∑ j : Fin n, EuclideanSpace.single j (1 : ℝ) :
      EuclideanSpace ℝ (Fin n))‖ ^ 2 = (n : ℝ) := bq_one_norm2
  have hexp := norm_sub_sq_real (EuclideanSpace.single i (1 : ℝ))
    ((n : ℝ)⁻¹ • ∑ j : Fin n, EuclideanSpace.single j (1 : ℝ))
  rw [inner_smul_right, hone, mul_one, h1] at hexp
  have hsmul : ‖(n : ℝ)⁻¹ • ∑ j : Fin n,
      EuclideanSpace.single j (1 : ℝ)‖ ^ 2
      = ((n : ℝ)⁻¹) ^ 2 * (n : ℝ) := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hnorm1]
  rw [hsmul] at hexp
  rw [hexp]
  field_simp
  ring

/-- Regular simplex configuration around a pair. -/
private theorem bq_exists_regular_simplex_config {n : ℕ} (hn : 2 ≤ n)
    (x y : EuclideanSpace ℝ (Fin n)) (hxy : x ≠ y)
    {s : ℝ} (hs : 0 < s) :
    ∃ v : Fin n → EuclideanSpace ℝ (Fin n),
      (∀ i j, i ≠ j → dist (v i) (v j) = s) ∧
      (∀ i, dist x (v i) ^ 2
        = dist x y ^ 2 / 4 + s ^ 2 * ((n : ℝ) - 1) / (2 * (n : ℝ))) ∧
      (∀ i, dist y (v i) ^ 2
        = dist x y ^ 2 / 4 + s ^ 2 * ((n : ℝ) - 1) / (2 * (n : ℝ))) := by
  have hn0 : n ≠ 0 := by omega
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  have hnPos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hsqrt_n_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnPos
  have hsqrt_n_ne : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt hsqrt_n_pos
  have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  -- distance and unit direction
  set d := dist x y with hd_def
  have hd : 0 < d := dist_pos.mpr hxy
  have hdne : d ≠ 0 := ne_of_gt hd
  have hnorm_yx : ‖y - x‖ = d := by
    rw [hd_def, ← dist_eq_norm, dist_comm]
  set u : EuclideanSpace ℝ (Fin n) := d⁻¹ • (y - x) with hu_def
  have hu1 : ‖u‖ = 1 := by
    rw [hu_def, norm_smul, Real.norm_eq_abs, hnorm_yx,
      abs_of_pos (inv_pos.mpr hd)]
    exact inv_mul_cancel₀ hdne
  -- all-ones vector and unit vector a
  set one : EuclideanSpace ℝ (Fin n)
    := ∑ j : Fin n, EuclideanSpace.single j (1 : ℝ) with hone_def
  have hone2 : ‖one‖ ^ 2 = (n : ℝ) := bq_one_norm2
  have hone_norm : ‖one‖ = Real.sqrt (n : ℝ) := by
    have hnn : (0 : ℝ) ≤ ‖one‖ := norm_nonneg _
    have hsq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) :=
      Real.sq_sqrt hnPos.le
    have hnn2 : (0 : ℝ) ≤ Real.sqrt (n : ℝ) :=
      Real.sqrt_nonneg _
    exact (pow_left_inj₀ hnn hnn2 two_ne_zero).mp (by rw [hone2, hsq])
  set a : EuclideanSpace ℝ (Fin n)
    := (Real.sqrt (n : ℝ))⁻¹ • one with ha_def
  have ha1 : ‖a‖ = 1 := by
    rw [ha_def, norm_smul, Real.norm_eq_abs, hone_norm,
      abs_of_pos (inv_pos.mpr hsqrt_n_pos)]
    exact inv_mul_cancel₀ hsqrt_n_ne
  -- reflection sending a to u
  set ρ : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)
    := Submodule.reflection (ℝ ∙ (a - u))ᗮ with hρ_def
  have hρa : ρ a = u := Submodule.reflection_sub (by rw [ha1, hu1])
  -- midpoint and scale
  set m : EuclideanSpace ℝ (Fin n) := ((1 / 2 : ℝ)) • (x + y) with hm_def
  have hsqrt2_ne : Real.sqrt 2 ≠ 0 := ne_of_gt hsqrt2_pos
  set c : ℝ := s / Real.sqrt 2 with hc_def
  have hc2 : c ^ 2 = s ^ 2 / 2 := by
    rw [hc_def, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  -- the simplex vertices
  refine ⟨fun i => m + c • ρ (EuclideanSpace.single i (1 : ℝ)
    - (n : ℝ)⁻¹ • one), ?_, ?_, ?_⟩
  · -- pairwise distances
    intro i j hij
    have hsub : (m + c • ρ (EuclideanSpace.single i (1 : ℝ) - (n : ℝ)⁻¹ • one))
        - (m + c • ρ (EuclideanSpace.single j (1 : ℝ) - (n : ℝ)⁻¹ • one))
        = c • ρ (EuclideanSpace.single i (1 : ℝ)
          - EuclideanSpace.single j (1 : ℝ)) := by
      have harg : (EuclideanSpace.single i (1 : ℝ) - (n : ℝ)⁻¹ • one)
          - (EuclideanSpace.single j (1 : ℝ) - (n : ℝ)⁻¹ • one)
          = EuclideanSpace.single i (1 : ℝ)
            - EuclideanSpace.single j (1 : ℝ) := by abel
      have e1 : (m + c • ρ (EuclideanSpace.single i (1 : ℝ)
          - (n : ℝ)⁻¹ • one))
          - (m + c • ρ (EuclideanSpace.single j (1 : ℝ) - (n : ℝ)⁻¹ • one))
          = c • (ρ (EuclideanSpace.single i (1 : ℝ) - (n : ℝ)⁻¹ • one)
            - ρ (EuclideanSpace.single j (1 : ℝ) - (n : ℝ)⁻¹ • one)) := by
        rw [smul_sub]
        abel
      have e2 : ρ (EuclideanSpace.single i (1 : ℝ) - (n : ℝ)⁻¹ • one)
          - ρ (EuclideanSpace.single j (1 : ℝ) - (n : ℝ)⁻¹ • one)
          = ρ (EuclideanSpace.single i (1 : ℝ)
            - EuclideanSpace.single j (1 : ℝ)) := by
        rw [← map_sub, harg]
      rw [e1, e2]
    have hnorm2 : ‖(m + c • ρ (EuclideanSpace.single i (1 : ℝ)
        - (n : ℝ)⁻¹ • one))
        - (m + c • ρ (EuclideanSpace.single j (1 : ℝ)
          - (n : ℝ)⁻¹ • one))‖ ^ 2 = s ^ 2 := by
      rw [hsub, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hc2,
        LinearIsometryEquiv.norm_map]
      rw [bq_single_sub_norm2 (fun h => hij h)]
      ring
    rw [← dist_eq_norm] at hnorm2
    exact (pow_left_inj₀ dist_nonneg hs.le two_ne_zero).mp hnorm2
  · -- helper facts shared by the two distance formulas
    have horth : ∀ i, ⟪(m + c • ρ (EuclideanSpace.single i (1 : ℝ)
        - (n : ℝ)⁻¹ • one)) - m, u⟫_ℝ = 0 := by
      intro i
      have hsub : (m + c • ρ (EuclideanSpace.single i (1 : ℝ)
          - (n : ℝ)⁻¹ • one)) - m
          = c • ρ (EuclideanSpace.single i (1 : ℝ) - (n : ℝ)⁻¹ • one) := by
        abel
      rw [hsub, real_inner_smul_left]
      have hinner : ⟪ρ (EuclideanSpace.single i (1 : ℝ) - (n : ℝ)⁻¹ • one),
          u⟫_ℝ = 0 := by
        conv_lhs => rw [← hρa]
        rw [LinearIsometryEquiv.inner_map_map]
        have hleft : ⟪EuclideanSpace.single i (1 : ℝ) - (n : ℝ)⁻¹ • one,
            one⟫_ℝ = 0 := by
          rw [inner_sub_left, real_inner_smul_left, bq_single_one_inner,
            real_inner_self_eq_norm_sq, bq_one_norm2,
            inv_mul_cancel₀ hnR, sub_self]
        have hrr : ⟪EuclideanSpace.single i (1 : ℝ) - (n : ℝ)⁻¹ • one,
            a⟫_ℝ = 0 := by
          rw [ha_def, inner_smul_right, hleft, mul_zero]
        exact hrr
      rw [hinner, mul_zero]
    have hrad : ∀ i, ‖(m + c • ρ (EuclideanSpace.single i (1 : ℝ)
        - (n : ℝ)⁻¹ • one)) - m‖ ^ 2
        = s ^ 2 * ((n : ℝ) - 1) / (2 * (n : ℝ)) := by
      intro i
      have hsub : (m + c • ρ (EuclideanSpace.single i (1 : ℝ)
          - (n : ℝ)⁻¹ • one)) - m
          = c • ρ (EuclideanSpace.single i (1 : ℝ) - (n : ℝ)⁻¹ • one) := by
        abel
      rw [hsub, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hc2,
        LinearIsometryEquiv.norm_map,
        bq_single_centered_norm2 hnR i]
      field_simp
    have hxm : x - m = -(((d / 2)) • u) := by
      have hhalf : ((d / 2)) • u = ((1 / 2 : ℝ)) • (y - x) := by
        rw [hu_def, ← mul_smul]
        congr 1
        field_simp
      have hxm2 : x - m = -(((1 / 2 : ℝ)) • (y - x)) := by
        rw [hm_def]
        module
      rw [hxm2, hhalf]
    have hym : y - m = (((d / 2)) • u) := by
      have hhalf : ((d / 2)) • u = ((1 / 2 : ℝ)) • (y - x) := by
        rw [hu_def, ← mul_smul]
        congr 1
        field_simp
      have hym2 : y - m = (((1 / 2 : ℝ)) • (y - x)) := by
        rw [hm_def]
        module
      rw [hym2, hhalf]
    have hxm_norm2 : ‖x - m‖ ^ 2 = d ^ 2 / 4 := by
      rw [hxm, norm_neg, norm_smul, hu1, mul_one, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0 : ℝ) < d / 2)]
      ring
    -- dist x formula
    intro i
    have hdecomp : x - (m + c • ρ (EuclideanSpace.single i (1 : ℝ)
        - (n : ℝ)⁻¹ • one))
        = (x - m) - ((m + c • ρ (EuclideanSpace.single i (1 : ℝ)
          - (n : ℝ)⁻¹ • one)) - m) := by abel
    have hcross : ⟪x - m, (m + c • ρ (EuclideanSpace.single i (1 : ℝ)
        - (n : ℝ)⁻¹ • one)) - m⟫_ℝ = 0 := by
      rw [hxm, inner_neg_left, real_inner_smul_left]
      have h0 := horth i
      rw [real_inner_comm] at h0
      rw [h0, mul_zero, neg_zero]
    have hexp := norm_sub_sq_real (x - m)
      ((m + c • ρ (EuclideanSpace.single i (1 : ℝ) - (n : ℝ)⁻¹ • one)) - m)
    rw [hcross, mul_zero, sub_zero] at hexp
    rw [← hdecomp, hxm_norm2, hrad i] at hexp
    rw [← dist_eq_norm, hd_def] at *
    linarith [hexp]
  · intro i
    have horth : ⟪(m + c • ρ (EuclideanSpace.single i (1 : ℝ)
        - (n : ℝ)⁻¹ • one)) - m, u⟫_ℝ = 0 := by
      have hsub : (m + c • ρ (EuclideanSpace.single i (1 : ℝ)
          - (n : ℝ)⁻¹ • one)) - m
          = c • ρ (EuclideanSpace.single i (1 : ℝ) - (n : ℝ)⁻¹ • one) := by
        abel
      rw [hsub, real_inner_smul_left]
      have hinner : ⟪ρ (EuclideanSpace.single i (1 : ℝ) - (n : ℝ)⁻¹ • one),
          u⟫_ℝ = 0 := by
        conv_lhs => rw [← hρa]
        rw [LinearIsometryEquiv.inner_map_map]
        have hleft : ⟪EuclideanSpace.single i (1 : ℝ) - (n : ℝ)⁻¹ • one,
            one⟫_ℝ = 0 := by
          rw [inner_sub_left, real_inner_smul_left, bq_single_one_inner,
            real_inner_self_eq_norm_sq, bq_one_norm2,
            inv_mul_cancel₀ hnR, sub_self]
        have hrr : ⟪EuclideanSpace.single i (1 : ℝ) - (n : ℝ)⁻¹ • one,
            a⟫_ℝ = 0 := by
          rw [ha_def, inner_smul_right, hleft, mul_zero]
        exact hrr
      rw [hinner, mul_zero]
    have hrad : ‖(m + c • ρ (EuclideanSpace.single i (1 : ℝ)
        - (n : ℝ)⁻¹ • one)) - m‖ ^ 2
        = s ^ 2 * ((n : ℝ) - 1) / (2 * (n : ℝ)) := by
      have hsub : (m + c • ρ (EuclideanSpace.single i (1 : ℝ)
          - (n : ℝ)⁻¹ • one)) - m
          = c • ρ (EuclideanSpace.single i (1 : ℝ) - (n : ℝ)⁻¹ • one) := by
        abel
      rw [hsub, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hc2,
        LinearIsometryEquiv.norm_map,
        bq_single_centered_norm2 hnR i]
      field_simp
    have hym : y - m = (((d / 2)) • u) := by
      have hhalf : ((d / 2)) • u = ((1 / 2 : ℝ)) • (y - x) := by
        rw [hu_def, ← mul_smul]
        congr 1
        field_simp
      have hym2 : y - m = (((1 / 2 : ℝ)) • (y - x)) := by
        rw [hm_def]
        module
      rw [hym2, hhalf]
    have hym_norm2 : ‖y - m‖ ^ 2 = d ^ 2 / 4 := by
      rw [hym, norm_smul, hu1, mul_one, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0 : ℝ) < d / 2)]
      ring
    have hdecomp : y - (m + c • ρ (EuclideanSpace.single i (1 : ℝ)
        - (n : ℝ)⁻¹ • one))
        = (y - m) - ((m + c • ρ (EuclideanSpace.single i (1 : ℝ)
          - (n : ℝ)⁻¹ • one)) - m) := by abel
    have hcross : ⟪y - m, (m + c • ρ (EuclideanSpace.single i (1 : ℝ)
        - (n : ℝ)⁻¹ • one)) - m⟫_ℝ = 0 := by
      rw [hym, real_inner_smul_left]
      have h0 := horth
      rw [real_inner_comm] at h0
      rw [h0, mul_zero]
    have hexp := norm_sub_sq_real (y - m)
      ((m + c • ρ (EuclideanSpace.single i (1 : ℝ) - (n : ℝ)⁻¹ • one)) - m)
    rw [hcross, mul_zero, sub_zero] at hexp
    rw [← hdecomp, hym_norm2, hrad] at hexp
    rw [← dist_eq_norm, hd_def] at *
    linarith [hexp]

/-- Rigidity gives weak preservation. -/
private theorem bq_wpres_of_regular_simplex {n : ℕ} (hn : 2 ≤ n)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (r s t : ℝ) (hs : 0 < s) (ht : 0 < t) (hr : 0 < r)
    (hformula : t ^ 2 = 4 * r ^ 2 - 2 * s ^ 2 * ((n : ℝ) - 1) / (n : ℝ))
    (hPr : ∀ x y, dist x y = r → dist (f x) (f y) = r)
    (hPs : ∀ x y, dist x y = s → dist (f x) (f y) = s) :
    ∀ x y, dist x y = t → dist (f x) (f y) = t ∨ f x = f y := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hnR : ((m : ℝ) + 2) ≠ 0 := by positivity
  intro x y hxy
  have hne : x ≠ y := by
    intro hcon
    rw [hcon, dist_self] at hxy
    linarith [ht]
  obtain ⟨v, hvdist, hvx, hvy⟩ :=
    bq_exists_regular_simplex_config (by omega : 2 ≤ m + 2) x y hne hs
  have hn_cast : ((m + 2 : ℕ) : ℝ) = (m : ℝ) + 2 := by push_cast; ring
  have hRval : t ^ 2 / 4 + s ^ 2 * (((m : ℝ) + 2) - 1) / (2 * ((m : ℝ) + 2))
      = r ^ 2 := by
    have hform : t ^ 2
        = 4 * r ^ 2 - 2 * s ^ 2 * (((m : ℝ) + 2) - 1) / ((m : ℝ) + 2) := by
      have h := hformula
      rw [hn_cast] at h
      exact h
    field_simp [hnR] at hform ⊢
    linarith
  have hpre : ∀ i, dist x (v i) = r := by
    intro i
    have h2 := hvx i
    rw [hn_cast, hxy] at h2
    rw [hRval] at h2
    have hnn : (0 : ℝ) ≤ dist x (v i) := dist_nonneg
    exact (pow_left_inj₀ hnn hr.le two_ne_zero).mp h2
  have hpre2 : ∀ i, dist y (v i) = r := by
    intro i
    have h2 := hvy i
    rw [hn_cast, hxy] at h2
    rw [hRval] at h2
    have hnn : (0 : ℝ) ≤ dist y (v i) := dist_nonneg
    exact (pow_left_inj₀ hnn hr.le two_ne_zero).mp h2
  have himg_dist : ∀ i j, i ≠ j → dist (f (v i)) (f (v j)) = s := by
    intro i j hij
    exact hPs _ _ (hvdist i j hij)
  have himg_x : ∀ i, dist (f x) (f (v i)) = r := fun i => hPr _ _ (hpre i)
  have himg_y : ∀ i, dist (f y) (f (v i)) = r := fun i => hPr _ _ (hpre2 i)
  have hN3 := bq_regular_simplex_apex_dichotomy hs (f ∘ v)
    (fun i j hij => himg_dist i j hij) (f x) (f y) r himg_x himg_y
  rcases hN3 with h | h
  · right
    exact h
  · left
    have ht2 : dist (f x) (f y) ^ 2 = t ^ 2 := by
      rw [h]
      have h2 := hformula
      rw [hn_cast] at h2
      have hbridge : ((m : ℝ) + 1) = (((m : ℝ) + 2) - 1) := by ring
      rw [hbridge, ← h2]
    have hnn : (0 : ℝ) ≤ dist (f x) (f y) := dist_nonneg
    exact (pow_left_inj₀ hnn ht.le two_ne_zero).mp ht2

/-- In dimension ≥ 2, every nonzero vector has a unit orthogonal vector. -/
private theorem bq_exists_unit_orthogonal {n : ℕ} (hn : 2 ≤ n)
    (v : EuclideanSpace ℝ (Fin n)) (hv : v ≠ 0) :
    ∃ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 ∧ ⟪v, w⟫_ℝ = 0 := by
  -- span{v} is 1-dimensional, hence not ⊤
  have hfin : Module.finrank ℝ (ℝ ∙ v) = 1 := finrank_span_singleton hv
  have hne : (ℝ ∙ v : Submodule ℝ (EuclideanSpace ℝ (Fin n))) ≠ ⊤ := by
    intro hcon
    rw [hcon, finrank_top ℝ _, finrank_euclideanSpace_fin] at hfin
    omega
  obtain ⟨w₀, hw₀⟩ : ∃ w₀, w₀ ∉ (ℝ ∙ v : Submodule ℝ (EuclideanSpace ℝ (Fin n))) := by
    by_contra hall
    apply hne
    rw [Submodule.eq_top_iff']
    intro x
    by_contra hx
    exact hall ⟨x, hx⟩
  -- Gram–Schmidt step
  have hvn : ‖v‖ ≠ 0 := fun h => hv (norm_eq_zero.mp h)
  have hv2 : (‖v‖ ^ 2) ≠ 0 := pow_ne_zero 2 hvn
  set w₁ : EuclideanSpace ℝ (Fin n) := w₀ - (⟪v, w₀⟫_ℝ / ‖v‖ ^ 2) • v with hw₁
  have horth : ⟪v, w₁⟫_ℝ = 0 := by
    rw [hw₁, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
    ring
  have hw₁ne : w₁ ≠ 0 := by
    intro hcon
    apply hw₀
    have h0 : w₀ = (⟪v, w₀⟫_ℝ / ‖v‖ ^ 2) • v := by
      rw [hw₁] at hcon
      simpa using eq_of_sub_eq_zero hcon
    rw [h0]
    exact Submodule.mem_span_singleton.mpr ⟨_, rfl⟩
  have hw₁n : ‖w₁‖ ≠ 0 := fun h => hw₁ne (norm_eq_zero.mp h)
  refine ⟨‖w₁‖⁻¹ • w₁, ?_, ?_⟩
  · rw [norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ hw₁n
  · rw [inner_smul_right, horth, mul_zero]

/-- Two spheres in ℝ^n (n ≥ 2) intersect when the triangle inequalities hold. -/
private theorem bq_sphere_inter_nonempty {n : ℕ} (hn : 2 ≤ n)
    (s₁ s₂ : ℝ) (hs₁ : 0 ≤ s₁) (hs₂ : 0 ≤ s₂)
    (x y : EuclideanSpace ℝ (Fin n))
    (hlo : |s₁ - s₂| ≤ dist x y) (hhi : dist x y ≤ s₁ + s₂) :
    ∃ z, dist x z = s₁ ∧ dist y z = s₂ := by
  by_cases hxy : x = y
  · subst hxy
    rw [dist_self] at hlo
    have heq : s₁ = s₂ :=
      sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hlo (abs_nonneg _)))
    subst heq
    by_cases hs : s₁ = 0
    · subst hs; exact ⟨x, by simp, by simp⟩
    · -- use a standard basis vector, which is already unit
      have hbasis : ‖EuclideanSpace.single (⟨0, by omega⟩ : Fin n) (1 : ℝ)‖ = 1 := by
        simp
      refine ⟨x + s₁ • EuclideanSpace.single (⟨0, by omega⟩ : Fin n) (1 : ℝ), ?_, ?_⟩ <;> {
        rw [dist_eq_norm, norm_sub_rev]
        have hsub : (x + s₁ • EuclideanSpace.single (⟨0, by omega⟩ : Fin n) (1 : ℝ)) - x
          = s₁ • EuclideanSpace.single (⟨0, by omega⟩ : Fin n) (1 : ℝ) := by abel
        rw [hsub, norm_smul, hbasis, mul_one, Real.norm_eq_abs, abs_of_nonneg hs₁]
      }
  · have hd : 0 < dist x y := dist_pos.mpr hxy
    have hdne : dist x y ≠ 0 := ne_of_gt hd
    set d := dist x y with hddef
    have hdir : ‖y - x‖ = d := by rw [hddef, norm_sub_rev, ← dist_eq_norm]
    -- unit direction from x to y
    set u : EuclideanSpace ℝ (Fin n) := d⁻¹ • (y - x) with hu
    have hu1 : ‖u‖ = 1 := by
      have hnn : (0 : ℝ) ≤ d⁻¹ := inv_nonneg.mpr (le_of_lt hd)
      rw [hu, norm_smul, Real.norm_eq_abs, abs_of_nonneg hnn, hdir]
      exact inv_mul_cancel₀ hdne
    -- unit vector orthogonal to y - x
    obtain ⟨w, hw1, hworth⟩ :=
      bq_exists_unit_orthogonal hn (y - x) (sub_ne_zero.mpr (Ne.symm hxy))
    have huw : ⟪u, w⟫_ℝ = 0 := by
      rw [hu, real_inner_smul_left, hworth, mul_zero]
    have hwu : ⟪w, u⟫_ℝ = 0 := by rw [real_inner_comm]; exact huw
    -- signed distance along u and height
    set a : ℝ := (s₁ ^ 2 - s₂ ^ 2 + d ^ 2) / (2 * d) with hadef
    have h2d : (0 : ℝ) < 2 * d := by linarith [hd]
    have h2dne : (2 : ℝ) * d ≠ 0 := ne_of_gt h2d
    -- key bounds: (s₁ - d)² ≤ s₂² and s₂² ≤ (s₁ + d)²
    have hle := abs_le.mp hlo
    have hA1 : (s₁ - d) ^ 2 ≤ s₂ ^ 2 := by
      apply sq_le_sq' _ _
      · linarith [hhi]
      · linarith [hle.2]
    have hA2 : s₂ ^ 2 ≤ (s₁ + d) ^ 2 := by
      apply sq_le_sq' _ _
      · have hsd : (0 : ℝ) ≤ s₁ + d := by linarith [hs₁, hd]
        linarith [hs₂]
      · linarith [hle.1]
    have hAbs : |s₁ ^ 2 - s₂ ^ 2 + d ^ 2| ≤ 2 * d * s₁ := by
      rw [abs_le]
      constructor
      · have h := hA2
        nlinarith [h]
      · have h := hA1
        nlinarith [h]
    have ha2 : a ^ 2 ≤ s₁ ^ 2 := by
      have hnn2 : (0 : ℝ) ≤ 2 * d * s₁ :=
        mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hd)) hs₁
      rw [hadef, div_pow, div_le_iff₀ (pow_pos h2d 2)]
      have hsq : s₁ ^ 2 * (2 * d) ^ 2 = (2 * d * s₁) ^ 2 := by ring
      rw [hsq]
      exact sq_le_sq.mpr (by rwa [abs_of_nonneg hnn2])
    set h : ℝ := Real.sqrt (s₁ ^ 2 - a ^ 2) with hhdef
    have hh2 : h ^ 2 = s₁ ^ 2 - a ^ 2 := Real.sq_sqrt (by linarith [ha2])
    have hau : ‖a • u‖ = |a| := by
      rw [norm_smul, hu1, mul_one, Real.norm_eq_abs]
    have hhw : ‖h • w‖ = |h| := by
      rw [norm_smul, hw1, mul_one, Real.norm_eq_abs]
    have euw : ⟪a • u, h • w⟫_ℝ = 0 := by
      rw [real_inner_smul_left, real_inner_smul_right, huw, mul_zero, mul_zero]
    -- the intersection point
    refine ⟨x + a • u + h • w, ?_, ?_⟩
    · -- dist x z = s₁
      have e1 : (x + a • u + h • w) - x = a • u + h • w := by abel
      have enorm : ‖a • u + h • w‖ ^ 2 = s₁ ^ 2 := by
        rw [norm_add_sq_real, euw, mul_zero, add_zero, hau, hhw, sq_abs, sq_abs, hh2]
        ring
      have hdist2 : dist x (x + a • u + h • w) ^ 2 = s₁ ^ 2 := by
        rw [dist_eq_norm, norm_sub_rev, e1]; exact enorm
      exact (pow_left_inj₀ dist_nonneg hs₁ two_ne_zero).mp hdist2
    · -- dist y z = s₂
      have hyx : y - x = d • u := by
        rw [hu, smul_inv_smul₀ hdne]
      have hxy' : x - y = -(d • u) := by rw [← hyx]; abel
      have e2 : (x + a • u + h • w) - y = -((d - a) • u) + h • w := by
        have hdecomp : (x + a • u + h • w) - y = (x - y) + (a • u + h • w) := by abel
        rw [hdecomp, hxy', ← neg_smul, ← add_assoc, ← add_smul]
        congr 1
        rw [← neg_smul]
        congr 1
        ring
      have hneg1 : ‖-((d - a) • u)‖ = |d - a| := by
        rw [norm_neg, norm_smul, hu1, mul_one, Real.norm_eq_abs]
      have hneg : ⟪-((d - a) • u), h • w⟫_ℝ = 0 := by
        rw [inner_neg_left, real_inner_smul_left, real_inner_smul_right, huw]
        ring
      have enorm : ‖(x + a • u + h • w) - y‖ ^ 2 = s₂ ^ 2 := by
        have hval : (d - a) ^ 2 + (s₁ ^ 2 - a ^ 2) = s₂ ^ 2 := by
          rw [hadef]; field_simp; ring
        rw [e2, norm_add_sq_real, hneg, mul_zero, add_zero, hneg1, hhw, sq_abs, sq_abs, hh2]
        linarith [hval]
      have hdist2 : dist y (x + a • u + h • w) ^ 2 = s₂ ^ 2 := by
        rw [dist_eq_norm, norm_sub_rev]; exact enorm
      exact (pow_left_inj₀ dist_nonneg hs₂ two_ne_zero).mp hdist2

/-- Kite configuration around a pair. -/
private theorem bq_exists_kite_config {n : ℕ} (hn : 2 ≤ n)
    (x y : EuclideanSpace ℝ (Fin n)) (hxy : x ≠ y) (σ τ : ℝ) :
    ∃ p q : EuclideanSpace ℝ (Fin n), dist p q = |σ - τ|
      ∧ dist x p ^ 2 = dist x y ^ 2 / 4 + σ ^ 2
      ∧ dist y p ^ 2 = dist x y ^ 2 / 4 + σ ^ 2
      ∧ dist x q ^ 2 = dist x y ^ 2 / 4 + τ ^ 2
      ∧ dist y q ^ 2 = dist x y ^ 2 / 4 + τ ^ 2 := by
  obtain ⟨u, hu1, huorth⟩ :=
    bq_exists_unit_orthogonal hn (y - x) (sub_ne_zero.mpr (Ne.symm hxy))
  set d := dist x y with hd_def
  have hnorm : ‖x - y‖ = d := (dist_eq_norm _ _).symm
  have hnorm2 : ‖y - x‖ = d := by rw [norm_sub_rev]; exact hnorm
  set m : EuclideanSpace ℝ (Fin n) := ((1 / 2 : ℝ)) • (x + y) with hm_def
  have hxm : x - m = ((1 / 2 : ℝ)) • (x - y) := by rw [hm_def]; module
  have hym : y - m = ((1 / 2 : ℝ)) • (y - x) := by rw [hm_def]; module
  have hxu : ⟪x - y, u⟫_ℝ = 0 := by
    have e : (x - y) = -((y - x)) := by abel
    rw [e, inner_neg_left, huorth, neg_zero]
  have hcross : ⟪x - m, u⟫_ℝ = 0 := by
    rw [hxm, real_inner_smul_left, hxu, mul_zero]
  have hcross2 : ⟪y - m, u⟫_ℝ = 0 := by
    rw [hym, real_inner_smul_left, huorth, mul_zero]
  have hxm2 : ‖x - m‖ ^ 2 = d ^ 2 / 4 := by
    have e : ‖x - m‖ = d / 2 := by
      rw [hxm, norm_smul, Real.norm_eq_abs, hnorm,
        abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      ring
    rw [e]; ring
  have hym2 : ‖y - m‖ ^ 2 = d ^ 2 / 4 := by
    have e : ‖y - m‖ = d / 2 := by
      rw [hym, norm_smul, Real.norm_eq_abs, hnorm2,
        abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      ring
    rw [e]; ring
  have hru : ∀ r : ℝ, ‖r • u‖ ^ 2 = r ^ 2 := by
    intro r
    rw [norm_smul, hu1, mul_one, Real.norm_eq_abs, sq_abs]
  have keyx : ∀ r : ℝ, ‖x - (m + r • u)‖ ^ 2 = d ^ 2 / 4 + r ^ 2 := by
    intro r
    have hdecomp : x - (m + r • u) = (x - m) - r • u := by abel
    have hexp := norm_sub_sq_real (x - m) (r • u)
    have hIr : ⟪x - m, r • u⟫_ℝ = 0 := by
      rw [real_inner_smul_right, hcross, mul_zero]
    rw [hIr, hru, mul_zero, sub_zero] at hexp
    rw [← hdecomp, hxm2] at hexp
    exact hexp
  have keyy : ∀ r : ℝ, ‖y - (m + r • u)‖ ^ 2 = d ^ 2 / 4 + r ^ 2 := by
    intro r
    have hdecomp : y - (m + r • u) = (y - m) - r • u := by abel
    have hexp := norm_sub_sq_real (y - m) (r • u)
    have hIr : ⟪y - m, r • u⟫_ℝ = 0 := by
      rw [real_inner_smul_right, hcross2, mul_zero]
    rw [hIr, hru, mul_zero, sub_zero] at hexp
    rw [← hdecomp, hym2] at hexp
    exact hexp
  have hpq : (m + σ • u) - (m + τ • u) = (σ - τ) • u := by
    have e : (m + σ • u) - (m + τ • u) = (σ • u - τ • u) := by abel
    rw [e, ← sub_smul]
  have hdistpq : dist (m + σ • u) (m + τ • u) = |σ - τ| := by
    rw [dist_eq_norm, hpq, norm_smul, hu1, mul_one, Real.norm_eq_abs]
  refine ⟨m + σ • u, m + τ • u, hdistpq, ?_, ?_, ?_, ?_⟩
  · have g := keyx σ
    rw [← dist_eq_norm, hd_def] at g
    exact g
  · have g := keyy σ
    rw [← dist_eq_norm, hd_def] at g
    exact g
  · have g := keyx τ
    rw [← dist_eq_norm, hd_def] at g
    exact g
  · have g := keyy τ
    rw [← dist_eq_norm, hd_def] at g
    exact g

/-- Arbitrarily small positive preserved distances force continuity. -/
private theorem bq_continuous_of_small_preserved {n : ℕ} (hn : 2 ≤ n)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hsmall : ∀ ε > 0, ∃ s, 0 < s ∧ s < ε ∧
      ∀ x y, dist x y = s → dist (f x) (f y) = s) :
    Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨s, hs0, hsε, hpres⟩ := hsmall (ε / 2) (by linarith)
  refine ⟨2 * s, by linarith, ?_⟩
  intro y hy
  have hdy : dist x y ≤ s + s := by
    rw [dist_comm]
    have : dist y x < 2 * s := hy
    linarith [this]
  obtain ⟨z, hxz, hyz⟩ := bq_sphere_inter_nonempty hn s s (le_of_lt hs0) (le_of_lt hs0)
    x y (by rw [sub_self, abs_zero]; exact dist_nonneg) hdy
  have h1 : dist (f x) (f z) = s := hpres x z hxz
  have h2 : dist (f y) (f z) = s := hpres y z hyz
  calc dist (f y) (f x) ≤ dist (f y) (f z) + dist (f z) (f x) := dist_triangle _ _ _
    _ = s + s := by rw [h2, dist_comm (f z) (f x), h1]
    _ < ε := by linarith [hsε]

/-- Continuity plus a dense set of preserved distances gives an isometry. -/
private theorem bq_isometry_of_dense_preserved
    {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hcont : Continuous f)
    (hdense : ∀ t : ℝ, 0 ≤ t →
      t ∈ closure {s : ℝ | 0 ≤ s ∧ ∀ x y, dist x y = s → dist (f x) (f y) = s}) :
    Isometry f := by
  apply Isometry.of_dist_eq
  intro x y
  by_cases hxy : x = y
  · subst hxy; simp
  · have hd : 0 < dist x y := dist_pos.mpr hxy
    have hdne : dist x y ≠ 0 := ne_of_gt hd
    obtain ⟨S, hSmem, hlim⟩ := mem_closure_iff_seq_limit.mp (hdense _ (le_of_lt hd))
    have hSnn : ∀ m, 0 ≤ S m := fun m => (hSmem m).1
    have hSpres : ∀ m x y, dist x y = S m → dist (f x) (f y) = S m :=
      fun m => (hSmem m).2
    have hSd : ∀ m, dist (y + ((S m / dist x y) • (x - y))) y = S m := by
      intro m
      have hsub : (y + ((S m / dist x y) • (x - y))) - y
          = (S m / dist x y) • (x - y) := by abel
      have hnn : (0 : ℝ) ≤ S m / dist x y := div_nonneg (hSnn m) (le_of_lt hd)
      rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hnn,
        ← dist_eq_norm]
      exact div_mul_cancel₀ _ hdne
    have hxtend : Filter.Tendsto (fun m => y + ((S m / dist x y) • (x - y)))
        Filter.atTop (nhds x) := by
      have h1 : Filter.Tendsto (fun m => S m / dist x y) Filter.atTop (nhds 1) := by
        have h1' : Filter.Tendsto (fun m => S m / dist x y) Filter.atTop
            (nhds (dist x y / dist x y)) := hlim.div_const _
        rwa [div_self hdne] at h1'
      have h2 : Filter.Tendsto (fun m => (S m / dist x y) • (x - y)) Filter.atTop
          (nhds ((1 : ℝ) • (x - y))) :=
        h1.smul tendsto_const_nhds
      have h3 := h2.const_add y
      rwa [one_smul, add_sub_cancel] at h3
    have hfd : Filter.Tendsto
        (fun m => dist (f (y + ((S m / dist x y) • (x - y)))) (f y))
        Filter.atTop (nhds (dist (f x) (f y))) :=
      ((hcont.tendsto x).comp hxtend).dist tendsto_const_nhds
    have hval : Filter.Tendsto
        (fun m => dist (f (y + ((S m / dist x y) • (x - y)))) (f y))
        Filter.atTop (nhds (dist x y)) := by
      have h_eq : (fun m => dist (f (y + ((S m / dist x y) • (x - y)))) (f y)) = S := by
        funext m
        exact hSpres m _ _ (hSd m)
      rw [h_eq]
      exact hlim
    exact tendsto_nhds_unique hfd hval

/-- No multiplicative relation between √(11/3) and 1/√3. -/
private theorem bq_no_unit_relation_kite : ∀ k j : ℕ,
    (Real.sqrt (11 / 3)) ^ k * (1 / Real.sqrt 3) ^ j = 1 → k = 0 ∧ j = 0 := by
  intro k j h
  have h3nn : (0 : ℝ) ≤ 3 := by norm_num
  have h113nn : (0 : ℝ) ≤ (11 / 3 : ℝ) := by norm_num
  -- square both sides: (11/3)^k * (1/3)^j = 1
  have hsq : ((11 / 3 : ℝ)) ^ k * ((1 / 3 : ℝ)) ^ j = 1 := by
    have h2 := congrArg (· ^ 2) h
    simp only [one_pow] at h2
    rw [mul_pow] at h2
    have e1 : ((Real.sqrt (11 / 3)) ^ k) ^ 2 = ((11 / 3 : ℝ)) ^ k := by
      rw [← pow_mul, show k * 2 = 2 * k from mul_comm _ _, pow_mul,
        Real.sq_sqrt h113nn]
    have e2 : ((1 / Real.sqrt 3) ^ j) ^ 2 = ((1 / 3 : ℝ)) ^ j := by
      rw [← pow_mul, show j * 2 = 2 * j from mul_comm _ _, pow_mul]
      congr 1
      rw [div_pow, one_pow, Real.sq_sqrt h3nn]
    rw [e1, e2] at h2
    exact h2
  -- clear denominators: 11^k = 3^(k+j) in ℝ
  have hR : (11 : ℝ) ^ k = 3 ^ (k + j) := by
    rw [div_pow, div_pow, one_pow, div_mul_div_comm, mul_one] at hsq
    have hden : (3 : ℝ) ^ k * 3 ^ j ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num))
    have heq := (div_eq_one_iff_eq hden).mp hsq
    rw [heq, ← pow_add]
  -- cast to ℕ
  have hN : 11 ^ k = 3 ^ (k + j) := by exact_mod_cast hR
  by_cases hk : k = 0
  · subst hk
    simp at hN
    -- hN : 1 = 3 ^ j
    have hj : j = 0 := by
      by_contra hj
      have hpos : 0 < j := Nat.pos_of_ne_zero hj
      have hlt : (1 : ℕ) < 3 ^ j := one_lt_pow₀ (by norm_num) (by omega)
      omega
    exact ⟨rfl, hj⟩
  · exfalso
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hdvd : 3 ∣ 11 ^ (k' + 1) := hN ▸ dvd_pow_self 3 (by omega : k' + 1 + j ≠ 0)
    have h11 : 3 ∣ 11 := Nat.prime_three.dvd_of_dvd_pow hdvd
    norm_num at h11

/-- Weak preservation plus a distinct preserved distance upgrades to preservation. -/
private theorem bq_pres_of_wpres {n : ℕ} (hn : 2 ≤ n)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (t e : ℝ) (he : 0 < e) (hle : e ≤ 2 * t) (hne : e ≠ t)
    (hw : ∀ x y, dist x y = t → dist (f x) (f y) = t ∨ f x = f y)
    (hpres : ∀ x y, dist x y = e → dist (f x) (f y) = e) :
    ∀ x y, dist x y = t → dist (f x) (f y) = t := by
  intro x y hxy
  have ht : 0 ≤ t := hxy ▸ dist_nonneg
  rcases hw x y hxy with h | hcollapse
  · exact h
  · by_cases ht0 : t = 0
    · subst ht0
      simp [hcollapse]
    · have htpos : 0 < t := lt_of_le_of_ne' ht ht0
      have htri1 : |e - t| ≤ dist x y := by
        rw [hxy, abs_le]
        constructor <;> linarith
      have htri2 : dist x y ≤ e + t := by
        rw [hxy]
        linarith [he.le]
      obtain ⟨z, hxz, hyz⟩ := bq_sphere_inter_nonempty hn e t he.le ht x y htri1 htri2
      have h1 : dist (f x) (f z) = e := hpres x z hxz
      rcases hw y z hyz with h2 | h2
      · rw [hcollapse] at h1
        rw [h1] at h2
        exact absurd h2 hne
      · rw [hcollapse, h2, dist_self] at h1
        linarith [he]

/-- Preservation scales by c = √(2(n+1)/n). -/
private theorem bq_pres_mul_c {n : ℕ} (hn : 2 ≤ n)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (d : ℝ) (hd : 0 < d)
    (hpres : ∀ x y, dist x y = d → dist (f x) (f y) = d) :
    ∀ x y, dist x y = Real.sqrt (2 * ((n : ℝ) + 1) / (n : ℝ)) * d →
      dist (f x) (f y) = Real.sqrt (2 * ((n : ℝ) + 1) / (n : ℝ)) * d := by
  have hn0 : n ≠ 0 := by omega
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  have hnPos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hX : (1 : ℝ) < 2 * ((n : ℝ) + 1) / (n : ℝ) := by
    field_simp
    linarith [hnPos]
  have hc : (1 : ℝ) < Real.sqrt (2 * ((n : ℝ) + 1) / (n : ℝ)) := by
    conv_lhs => rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by norm_num) hX
  have hc0 : (0 : ℝ) < Real.sqrt (2 * ((n : ℝ) + 1) / (n : ℝ)) :=
    lt_trans zero_lt_one hc
  set c : ℝ := Real.sqrt (2 * ((n : ℝ) + 1) / (n : ℝ)) with hc_def
  have ht : 0 < c * d := mul_pos hc0 hd
  have hcsq : c ^ 2 = 2 * ((n : ℝ) + 1) / (n : ℝ) :=
    Real.sq_sqrt (zero_le_one.trans hX.le)
  have hformula : (c * d) ^ 2
      = 4 * d ^ 2 - 2 * d ^ 2 * ((n : ℝ) - 1) / (n : ℝ) := by
    rw [mul_pow, hcsq]
    field_simp
    ring
  have hw := bq_wpres_of_regular_simplex hn f d d (c * d) hd ht hd
    hformula hpres hpres
  have hle : d ≤ 2 * (c * d) := by
    have h12 : (1 : ℝ) ≤ 2 * c := by linarith [hc]
    have h := (le_mul_iff_one_le_right hd).mpr h12
    linarith [h]
  have hne : d ≠ c * d := by
    intro hcon
    have h1 : c * d = 1 * d := by rw [one_mul]; exact hcon.symm
    have hc1 : c = 1 := mul_right_cancel₀ (ne_of_gt hd) h1
    linarith [hc]
  exact bq_pres_of_wpres hn f (c * d) d hd hle hne hw hpres

/-- 1 < c and 0 < q < 1 for n ≥ 3. -/
private theorem bq_cq_bounds {n : ℕ} (hn : 3 ≤ n) :
    (1 : ℝ) < Real.sqrt (2 * ((n : ℝ) + 1) / (n : ℝ))
    ∧ 0 < (2 : ℝ) / (n : ℝ) ∧ (2 : ℝ) / (n : ℝ) < 1 := by
  have hnPos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hX : (1 : ℝ) < 2 * ((n : ℝ) + 1) / (n : ℝ) := by
    field_simp
    linarith [hnPos]
  have hc : (1 : ℝ) < Real.sqrt (2 * ((n : ℝ) + 1) / (n : ℝ)) := by
    conv_lhs => rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by norm_num) hX
  refine ⟨hc, div_pos (by norm_num) hnPos, ?_⟩
  rw [div_lt_one hnPos]
  have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  linarith [this]

/-- Dirichlet gives an arbitrarily small nonzero ℕ-combination. -/
private theorem bq_kronecker_step {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hirr : Irrational (α / β)) {ε : ℝ} (hε : 0 < ε) :
    ∃ k j : ℕ, 0 < |((k : ℝ) * α - (j : ℝ) * β)| ∧
      |((k : ℝ) * α - (j : ℝ) * β)| < ε := by
  have hβR : β ≠ 0 := ne_of_gt hβ
  have hξ : (0 : ℝ) < α / β := div_pos hα hβ
  obtain ⟨N, hN⟩ := exists_nat_gt (β / ε)
  set nn : ℕ := N + 1 with hnn_def
  have hn_pos : 0 < nn := by omega
  obtain ⟨p, q, hq0, hqn, happrox⟩ :=
    Real.exists_int_int_abs_mul_sub_le (α / β) hn_pos
  -- q > 0 as a real
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
  have hqξ : (0 : ℝ) < (q : ℝ) * (α / β) := mul_pos hqR hξ
  -- 1/(nn+1) ≤ 1/2
  have hnnR : (1 : ℝ) / (nn + 1) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num)
    have : (2 : ℝ) ≤ (nn : ℝ) + 1 := by
      have : 1 ≤ nn := hn_pos
      have hN1 : (1 : ℝ) ≤ (nn : ℝ) := by exact_mod_cast this
      linarith [hN1]
    exact this
  -- p ≥ 0
  have hp0 : 0 ≤ p := by
    by_contra hlt
    push Not at hlt
    have hle : p ≤ -1 := by omega
    have hcast : (p : ℝ) ≤ -1 := by exact_mod_cast hle
    have hbnd : (q : ℝ) * (α / β) - (p : ℝ) ≤ 1 / (nn + 1) :=
      (abs_le.mp happrox).2
    have hge : (q : ℝ) * (α / β) - (p : ℝ) > -1 := by linarith [hqξ, hcast]
    have hle2 : (1 : ℝ) / (nn + 1) ≤ 1 := le_trans hnnR (by norm_num)
    linarith [hbnd, hge, hle2]
  have hkR : ((q.toNat : ℕ) : ℝ) = (q : ℝ) := by
    have h1 : ((q.toNat : ℕ) : ℤ) = q := Int.toNat_of_nonneg hq0.le
    exact_mod_cast h1
  have hjR : ((p.toNat : ℕ) : ℝ) = (p : ℝ) := by
    have h1 : ((p.toNat : ℕ) : ℤ) = p := Int.toNat_of_nonneg hp0
    exact_mod_cast h1
  have hδeq : (q.toNat : ℝ) * α - (p.toNat : ℝ) * β
      = β * ((q : ℝ) * (α / β) - (p : ℝ)) := by
    rw [hkR, hjR]
    field_simp
  -- the Dirichlet error is nonzero by irrationality
  have hne : (q : ℝ) * (α / β) - (p : ℝ) ≠ 0 := by
    intro h0
    have h1 : (q : ℝ) * (α / β) = (p : ℝ) := by linarith [h0]
    have hqa : (q : ℝ) * α = (p : ℝ) * β := by
      calc (q : ℝ) * α = ((q : ℝ) * (α / β)) * β := by
            rw [mul_assoc, div_mul_cancel₀ _ hβR]
        _ = (p : ℝ) * β := by rw [h1]
    have hrat : α / β = (((p / q : ℚ)) : ℝ) := by
      rw [Rat.cast_div]
      push_cast
      rw [div_eq_div_iff hβR (by exact_mod_cast ne_of_gt hq0)]
      linear_combination hqa
    exact hirr ⟨_, hrat.symm⟩
  -- smallness: β/(nn+1) < ε
  have hsmall : β / ((nn : ℝ) + 1) < ε := by
    have hN' : β / ε < (N : ℝ) := hN
    have hbe : β < (N : ℝ) * ε := by
      rwa [div_lt_iff₀ hε] at hN'
    have hden : (0 : ℝ) < (nn : ℝ) + 1 := by
      have hN1 : (0 : ℝ) ≤ (nn : ℝ) := Nat.cast_nonneg _
      linarith [hN1]
    have hnn_cast : ((nn : ℕ) : ℝ) = (N : ℝ) + 1 := by
      rw [hnn_def]
      push_cast
      ring
    rw [hnn_cast]
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) + 1 + 1)]
    nlinarith [hbe, hε, Nat.cast_nonneg (α := ℝ) N]
  have hδabs : |(q.toNat : ℝ) * α - (p.toNat : ℝ) * β|
      = β * |(q : ℝ) * (α / β) - (p : ℝ)| := by
    rw [hδeq, abs_mul, abs_of_pos hβ]
  have happrox_le : |(q : ℝ) * (α / β) - (p : ℝ)| ≤ 1 / ((nn : ℝ) + 1) :=
    happrox
  refine ⟨q.toNat, p.toNat, ?_, ?_⟩
  · rw [hδabs]
    exact mul_pos hβ (abs_pos.mpr hne)
  · rw [hδabs]
    calc β * |(q : ℝ) * (α / β) - (p : ℝ)|
        ≤ β * (1 / ((nn : ℝ) + 1)) := by
          apply mul_le_mul_of_nonneg_left happrox_le hβ.le
      _ = β / ((nn : ℝ) + 1) := by rw [mul_one_div]
      _ < ε := hsmall

/-- ℕ-combinations kα − jβ are dense. -/
private theorem bq_additive_dense {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hirr : Irrational (α / β)) (T ε : ℝ) (hε : 0 < ε) :
    ∃ k j : ℕ, |(((k : ℝ) * α - (j : ℝ) * β) - T)| < ε := by
  obtain ⟨k₀, j₀, hpos, hsmall⟩ := bq_kronecker_step hα hβ hirr hε
  set δ : ℝ := (k₀ : ℝ) * α - (j₀ : ℝ) * β with hδdef
  have hne : δ ≠ 0 := abs_pos.mp hpos
  rcases lt_or_gt_of_ne hne with hneg | hposδ
  · -- δ < 0: shift target down by Kα, approximate with multiples going to −∞
    obtain ⟨K, hK⟩ := exists_nat_gt (T / α)
    have hKa : T < (K : ℝ) * α := by
      have h1 : T / α < (K : ℝ) := hK
      rwa [div_lt_iff₀ hα] at h1
    set T2 : ℝ := T - (K : ℝ) * α with hT2def
    have hT2 : T2 ≤ 0 := by linarith [hKa]
    set e : ℝ := -δ with he_def
    have he : 0 < e := by linarith [hneg]
    set L : ℕ := ⌊(-T2) / e⌋₊ with hLdef
    have hL1 : T2 ≤ (L : ℝ) * δ := by
      have hf : (L : ℝ) ≤ (-T2) / e :=
        Nat.floor_le (div_nonneg (by linarith [hT2]) he.le)
      have hf2 : (L : ℝ) * e ≤ -T2 := by rwa [le_div_iff₀ he] at hf
      rw [he_def] at hf2
      linarith [hf2]
    have hL2 : ((L : ℝ) + 1) * δ < T2 := by
      have hf : (-T2) / e < (L : ℝ) + 1 := Nat.lt_floor_add_one _
      have hf2 : -T2 < ((L : ℝ) + 1) * e := by rwa [div_lt_iff₀ he] at hf
      rw [he_def] at hf2
      linarith [hf2]
    have hclose : |(L : ℝ) * δ - T2| < ε := by
      have habs : |δ| = -δ := abs_of_neg hneg
      rw [abs_lt]
      constructor <;> linarith [hL1, hL2, hsmall, habs, hε]
    refine ⟨L * k₀ + K, L * j₀, ?_⟩
    have hkj : ((L * k₀ + K : ℕ) : ℝ) * α - ((L * j₀ : ℕ) : ℝ) * β
        = (L : ℝ) * δ + (K : ℝ) * α := by
      push_cast
      rw [hδdef]
      ring
    have hTeq : ((L * k₀ + K : ℕ) : ℝ) * α - ((L * j₀ : ℕ) : ℝ) * β - T
        = (L : ℝ) * δ - T2 := by
      rw [hkj, hT2def]
      ring
    rw [hTeq]
    exact hclose
  · -- δ > 0: shift target up by Jβ, approximate with multiples going to +∞
    obtain ⟨J, hJ⟩ := exists_nat_gt ((-T) / β)
    have hJa : -T < (J : ℝ) * β := by
      have h1 : (-T) / β < (J : ℝ) := hJ
      rwa [div_lt_iff₀ hβ] at h1
    set T2 : ℝ := T + (J : ℝ) * β with hT2def
    have hT2 : 0 ≤ T2 := by linarith [hJa]
    set L : ℕ := ⌊T2 / δ⌋₊ with hLdef
    have hL1 : (L : ℝ) * δ ≤ T2 := by
      have hf : (L : ℝ) ≤ T2 / δ :=
        Nat.floor_le (div_nonneg hT2 hposδ.le)
      rwa [le_div_iff₀ hposδ] at hf
    have hL2 : T2 < ((L : ℝ) + 1) * δ := by
      have hf : T2 / δ < (L : ℝ) + 1 := Nat.lt_floor_add_one _
      rwa [div_lt_iff₀ hposδ] at hf
    have hclose : |(L : ℝ) * δ - T2| < ε := by
      have habs : |δ| = δ := abs_of_pos hposδ
      rw [abs_lt]
      constructor <;> linarith [hL1, hL2, hsmall, habs, hε]
    refine ⟨L * k₀, L * j₀ + J, ?_⟩
    have hkj : ((L * k₀ : ℕ) : ℝ) * α - ((L * j₀ + J : ℕ) : ℝ) * β
        = (L : ℝ) * δ - (J : ℝ) * β := by
      push_cast
      rw [hδdef]
      ring
    have hTeq : ((L * k₀ : ℕ) : ℝ) * α - ((L * j₀ + J : ℕ) : ℝ) * β - T
        = (L : ℝ) * δ - T2 := by
      rw [hkj, hT2def]
      ring
    rw [hTeq]
    exact hclose

/-- Log ratio is irrational when powers never hit 1. -/
private theorem bq_log_irrational {A B : ℝ} (hA : 1 < A) (hB0 : 0 < B)
    (hB1 : B < 1)
    (H : ∀ k j : ℕ, A ^ k * B ^ j = 1 → k = 0 ∧ j = 0) :
    Irrational (Real.log A / (-Real.log B)) := by
  have hA0 : (0 : ℝ) < A := by linarith [hA]
  have hlogA : 0 < Real.log A := Real.log_pos hA
  have hlogB : Real.log B < 0 := Real.log_neg hB0 hB1
  have hβ : (0 : ℝ) < -Real.log B := by linarith [hlogB]
  intro hcon
  obtain ⟨r, hr⟩ := hcon
  have hrpos : (0 : ℝ) < ((r : ℚ) : ℝ) := by
    rw [hr]
    exact div_pos hlogA hβ
  have hrQ : 0 < r := Rat.cast_pos.mp hrpos
  have hnum : 0 < r.num := Rat.num_pos.mpr hrQ
  have hden : 0 < r.den := r.pos
  -- clear to naturals
  have hnumR : ((r.num.toNat : ℕ) : ℝ) = ((r.num : ℤ) : ℝ) := by
    have h1 : ((r.num.toNat : ℕ) : ℤ) = r.num :=
      Int.toNat_of_nonneg (le_of_lt hnum)
    exact_mod_cast h1
  have hqr : ((r : ℚ) : ℝ)
      = ((r.num : ℤ) : ℝ) / ((r.den : ℕ) : ℝ) := by
    have h := Rat.num_div_den r
    have h2 := congrArg ((↑) : ℚ → ℝ) h
    simp only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] at h2
    exact h2.symm
  have hrel : Real.log A / (-Real.log B) = ((r : ℚ) : ℝ) := hr.symm
  have hcross : (r.num.toNat : ℝ) * (-Real.log B)
      = (r.den : ℝ) * Real.log A := by
    have h1 : Real.log A * ((r.den : ℕ) : ℝ)
        = ((r.num : ℤ) : ℝ) * (-Real.log B) := by
      have h2 : Real.log A / (-Real.log B)
          = ((r.num : ℤ) : ℝ) / ((r.den : ℕ) : ℝ) := by rw [hrel, hqr]
      have hdenR : ((r.den : ℕ) : ℝ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (ne_of_gt hden)
      rw [div_eq_div_iff (ne_of_gt hβ) hdenR] at h2
      linarith [h2]
    rw [hnumR]
    linarith [h1]
  -- exponentiate to a unit relation
  have hApos : (0 : ℝ) < A ^ r.den := pow_pos hA0 _
  have hBpos : (0 : ℝ) < B ^ r.num.toNat := pow_pos hB0 _
  have hlog_eq : Real.log (A ^ r.den * B ^ r.num.toNat) = 0 := by
    rw [Real.log_mul (ne_of_gt hApos) (ne_of_gt hBpos),
      Real.log_pow, Real.log_pow]
    linarith [hcross]
  have hunit : A ^ r.den * B ^ r.num.toNat = 1 := by
    have h := Real.exp_log (mul_pos hApos hBpos)
    rw [hlog_eq, Real.exp_zero] at h
    exact h.symm
  have hcon2 := H r.den r.num.toNat hunit
  have : r.den ≠ 0 := ne_of_gt hden
  exact this hcon2.1

/-- Density of A^k B^j in (0, ∞). -/
private theorem bq_dense_pow_mul_pow (A B : ℝ) (hA : 1 < A)
    (hB0 : 0 < B) (hB1 : B < 1)
    (H : ∀ k j : ℕ, A ^ k * B ^ j = 1 → k = 0 ∧ j = 0)
    (t ε : ℝ) (ht : 0 < t) (hε : 0 < ε) :
    ∃ k j : ℕ, |A ^ k * B ^ j - t| < ε := by
  have hA0 : (0 : ℝ) < A := by linarith [hA]
  have hα : (0 : ℝ) < Real.log A := Real.log_pos hA
  have hβ : (0 : ℝ) < -Real.log B := by
    have h := Real.log_neg hB0 hB1
    linarith [h]
  have hirr := bq_log_irrational hA hB0 hB1 H
  -- continuity of exp at log t
  have hca : ContinuousAt Real.exp (Real.log t) :=
    Real.continuous_exp.continuousAt (x := Real.log t)
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.mp hca ε hε
  obtain ⟨k, j, hkj⟩ :=
    bq_additive_dense hα hβ hirr (Real.log t) δ hδ
  have hexp_eq : A ^ k * B ^ j
      = Real.exp ((k : ℝ) * Real.log A - (j : ℝ) * (-Real.log B)) := by
    have eA : A ^ k = Real.exp ((k : ℝ) * Real.log A) := by
      rw [Real.exp_nat_mul, Real.exp_log hA0]
    have eB : B ^ j = Real.exp ((j : ℝ) * Real.log B) := by
      rw [Real.exp_nat_mul, Real.exp_log hB0]
    have eB2 : Real.exp ((j : ℝ) * Real.log B)
        = Real.exp (-((j : ℝ) * (-Real.log B))) := by congr 1; ring
    rw [eA, eB, eB2, ← Real.exp_add]
    congr 1
  have hdist : dist ((k : ℝ) * Real.log A - (j : ℝ) * (-Real.log B))
      (Real.log t) < δ := by
    rwa [Real.dist_eq]
  have himg := hcont hdist
  rw [Real.dist_eq, Real.exp_log ht] at himg
  exact ⟨k, j, by rwa [hexp_eq]⟩

/-- No multiplicative relation between c and q for n ≥ 3. -/
private theorem bq_no_unit_relation_simplex {n : ℕ} (hn : 3 ≤ n) (k j : ℕ)
    (h : (Real.sqrt (2 * ((n : ℝ) + 1) / (n : ℝ))) ^ k * ((2 : ℝ) / (n : ℝ)) ^ j
      = 1) :
    k = 0 ∧ j = 0 := by
  have hnPos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnR : (n : ℝ) ≠ 0 := ne_of_gt hnPos
  have hX : (1 : ℝ) < 2 * ((n : ℝ) + 1) / (n : ℝ) := by
    field_simp
    linarith [hnPos]
  have hXnn : (0 : ℝ) ≤ 2 * ((n : ℝ) + 1) / (n : ℝ) :=
    zero_le_one.trans hX.le
  set c : ℝ := Real.sqrt (2 * ((n : ℝ) + 1) / (n : ℝ)) with hc_def
  set q : ℝ := (2 : ℝ) / (n : ℝ) with hq_def
  have ec : c ^ 2 = 2 * ((n : ℝ) + 1) / (n : ℝ) := Real.sq_sqrt hXnn
  have eqq : q ^ 2 = 4 / (n : ℝ) ^ 2 := by
    rw [hq_def, div_pow]
    norm_num
  -- square the relation
  have hsq : (2 * ((n : ℝ) + 1) / (n : ℝ)) ^ k * (4 / (n : ℝ) ^ 2) ^ j
      = 1 := by
    have h2 := congrArg (· ^ 2) h
    simp only [one_pow] at h2
    rw [mul_pow] at h2
    have e1 : (c ^ k) ^ 2 = (c ^ 2) ^ k := by
      rw [← pow_mul, ← pow_mul, mul_comm k 2]
    have e2 : (q ^ j) ^ 2 = (q ^ 2) ^ j := by
      rw [← pow_mul, ← pow_mul, mul_comm j 2]
    rw [e1, e2, ec, eqq] at h2
    exact h2
  -- clear denominators to a Nat equation
  have hR : (2 : ℝ) ^ k * ((n : ℝ) + 1) ^ k * (4 : ℝ) ^ j
      = (n : ℝ) ^ (k + 2 * j) := by
    rw [div_pow, div_pow, div_mul_div_comm] at hsq
    have hden : (n : ℝ) ^ k * ((n : ℝ) ^ 2) ^ j ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hnR) (pow_ne_zero _ (pow_ne_zero _ hnR))
    have heq := (div_eq_one_iff_eq hden).mp hsq
    rw [mul_pow] at heq
    have hrhs : (n : ℝ) ^ k * ((n : ℝ) ^ 2) ^ j = (n : ℝ) ^ (k + 2 * j) := by
      rw [← pow_mul, ← pow_add]
    rw [hrhs] at heq
    exact heq
  -- cast to ℕ
  have hN : 2 ^ k * (n + 1) ^ k * 4 ^ j = n ^ (k + 2 * j) := by
    have hR2 := hR
    exact_mod_cast hR2
  -- (n+1)^k divides a power of n, hence equals 1
  have hdvd : (n + 1) ^ k ∣ n ^ (k + 2 * j) := by
    refine ⟨2 ^ k * 4 ^ j, ?_⟩
    rw [← hN]
    ring
  have hcop : Nat.Coprime (n + 1) n :=
    Nat.coprime_self_add_left.mpr ((Nat.coprime_one_left_iff n).mpr trivial)
  have hcop_pow : Nat.Coprime ((n + 1) ^ k) (n ^ (k + 2 * j)) :=
    hcop.pow _ _
  have hk1 : (n + 1) ^ k = 1 := hcop_pow.eq_one_of_dvd hdvd
  have hk0 : k = 0 := by
    rcases (Nat.pow_eq_one.mp hk1) with h | h
    · exfalso
      have : 1 < n + 1 := by omega
      omega
    · exact h
  subst hk0
  simp only [pow_zero, one_mul] at hN
  -- hN : 4 ^ j = n ^ (0 + 2 * j)
  have h4j : (4 : ℕ) ^ j = n ^ (2 * j) := by
    have h := hN
    simp only [zero_add] at h
    exact h
  have h42 : (4 : ℕ) ^ j = (n ^ 2) ^ j := by
    rw [← pow_mul]
    exact h4j
  by_cases hj : j = 0
  · exact ⟨rfl, hj⟩
  · exfalso
    have h4eq : (4 : ℕ) = n ^ 2 := Nat.pow_left_injective hj h42
    have hn2 : n = 2 := by
      have h22 : (2 : ℕ) ^ 2 = n ^ 2 := by rw [← h4eq]; norm_num
      exact Nat.pow_left_injective two_ne_zero h22.symm
    omega

/-- All c^k q^j preserved for n ≥ 3. -/
private theorem bq_pres_pow_of_three_le {n : ℕ} (hn : 3 ≤ n)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf : ∀ x y, dist x y = 1 → dist (f x) (f y) = 1) :
    ∀ k j : ℕ, ∀ x y,
      dist x y
        = (Real.sqrt (2 * ((n : ℝ) + 1) / (n : ℝ))) ^ k * ((2 : ℝ) / (n : ℝ)) ^ j →
      dist (f x) (f y)
        = (Real.sqrt (2 * ((n : ℝ) + 1) / (n : ℝ))) ^ k * ((2 : ℝ) / (n : ℝ)) ^ j := by
  have hn2 : 2 ≤ n := by omega
  have hnPos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  obtain ⟨hc1, hq0, hq1⟩ := bq_cq_bounds hn
  set c : ℝ := Real.sqrt (2 * ((n : ℝ) + 1) / (n : ℝ)) with hc_def
  set q : ℝ := (2 : ℝ) / (n : ℝ) with hq_def
  have hc0 : (0 : ℝ) < c := by linarith [hc1]
  have hXpos : (0 : ℝ) < 2 * ((n : ℝ) + 1) / (n : ℝ) :=
    div_pos (by linarith [hnPos]) hnPos
  have hcsq : c ^ 2 = 2 * ((n : ℝ) + 1) / (n : ℝ) := by
    rw [hc_def]
    exact Real.sq_sqrt hXpos.le
  have Hrel : ∀ k j : ℕ, c ^ k * q ^ j = 1 → k = 0 ∧ j = 0 := by
    intro k j h
    exact bq_no_unit_relation_simplex hn k j h
  -- Step 1: Pres (c^k)
  have step1 : ∀ k x y, dist x y = c ^ k → dist (f x) (f y) = c ^ k := by
    intro k
    induction k with
    | zero =>
      intro x y hxy
      simp only [pow_zero] at hxy ⊢
      exact hf x y hxy
    | succ k ih =>
      intro x y hxy
      have hpos : (0 : ℝ) < c ^ k := pow_pos hc0 _
      have hstep := bq_pres_mul_c hn2 f (c ^ k) hpos (ih)
      have heq : c ^ (k + 1) = c * c ^ k := pow_succ' c k
      rw [heq] at hxy ⊢
      exact hstep x y hxy
  -- Step 2: WPres (q*d) from Pres d and Pres (c*d)
  have step2 : ∀ d : ℝ, 0 < d →
      (∀ x y, dist x y = d → dist (f x) (f y) = d) →
      (∀ x y, dist x y = c * d → dist (f x) (f y) = c * d) →
      ∀ x y, dist x y = q * d → dist (f x) (f y) = q * d ∨ f x = f y := by
    intro d hd hPd hPcd x y hxy
    have hcd : (0 : ℝ) < c * d := mul_pos hc0 hd
    have hqd : (0 : ℝ) < q * d := mul_pos hq0 hd
    have hformula : (q * d) ^ 2
        = 4 * d ^ 2 - 2 * (c * d) ^ 2 * ((n : ℝ) - 1) / (n : ℝ) := by
      rw [hq_def, mul_pow, mul_pow, hcsq]
      have hnR : (n : ℝ) ≠ 0 := ne_of_gt hnPos
      field_simp
      ring
    exact bq_wpres_of_regular_simplex hn2 f d (c * d) (q * d) hcd hqd hd
      hformula hPd hPcd x y hxy
  -- Step 3: bounded induction
  have step3 : ∀ j k, c ^ k * q ^ j ≥ 1 / 2 →
      ∀ x y, dist x y = c ^ k * q ^ j → dist (f x) (f y) = c ^ k * q ^ j := by
    intro j
    induction j with
    | zero =>
      intro k _ x y hxy
      simp only [pow_zero, mul_one] at hxy ⊢
      exact step1 k x y hxy
    | succ j ih =>
      intro k hk x y hxy
      have hqj : (0 : ℝ) < q ^ j := pow_pos hq0 _
      have hck : (0 : ℝ) < c ^ k := pow_pos hc0 _
      have hpos0 : (0 : ℝ) < c ^ k * q ^ j := mul_pos hck hqj
      have hge1 : c ^ k * q ^ j ≥ 1 / 2 := by
        have e : c ^ k * q ^ (j + 1) = (c ^ k * q ^ j) * q := by
          rw [pow_succ]
          ring
        have hle : (c ^ k * q ^ j) * q ≤ (c ^ k * q ^ j) * 1 :=
          mul_le_mul_of_nonneg_left hq1.le hpos0.le
        rw [mul_one] at hle
        linarith [hk, e, hle]
      have hge2 : c ^ (k + 1) * q ^ j ≥ 1 / 2 := by
        have e : c ^ (k + 1) * q ^ j = c * (c ^ k * q ^ j) := by
          rw [pow_succ']
          ring
        have hle : (1 : ℝ) * (c ^ k * q ^ j) ≤ c * (c ^ k * q ^ j) :=
          mul_le_mul_of_nonneg_right hc1.le hpos0.le
        rw [one_mul] at hle
        linarith [hge1, e, hle]
      have hPd := ih k hge1
      have hPcd : ∀ x y, dist x y = c * (c ^ k * q ^ j) →
          dist (f x) (f y) = c * (c ^ k * q ^ j) := by
        have h := ih (k + 1) hge2
        have e : c ^ (k + 1) * q ^ j = c * (c ^ k * q ^ j) := by
          rw [pow_succ']
          ring
        rwa [e] at h
      have hw := step2 (c ^ k * q ^ j) hpos0 hPd hPcd
      have e3 : c ^ k * q ^ (j + 1) = q * (c ^ k * q ^ j) := by
        rw [pow_succ]
        ring
      have hw2 : ∀ x y, dist x y = c ^ k * q ^ (j + 1) →
          dist (f x) (f y) = c ^ k * q ^ (j + 1) ∨ f x = f y := by
        rw [e3]
        exact hw
      have h12 : (1 : ℝ) ≤ 2 * (c ^ k * q ^ (j + 1)) := by linarith [hk]
      have hne : (1 : ℝ) ≠ c ^ k * q ^ (j + 1) := by
        intro hcon
        have h0 := Hrel k (j + 1) hcon.symm
        omega
      exact bq_pres_of_wpres hn2 f (c ^ k * q ^ (j + 1)) 1 zero_lt_one h12
        hne hw2 hf x y hxy
  -- Step 4: injectivity
  have hinj : Function.Injective f := by
    intro x y hfeq
    by_contra hne
    have htp : (0 : ℝ) < dist x y := dist_pos.mpr hne
    set t : ℝ := dist x y with ht_def
    set M : ℝ := max 1 t with hM_def
    have hM1 : (1 : ℝ) ≤ M := le_max_left _ _
    have hMt : t ≤ M := le_max_right _ _
    obtain ⟨k1, j1, hu⟩ := bq_dense_pow_mul_pow c q hc1 hq0 hq1 Hrel
      (M + t / 4) (t / 4) (by linarith [hM1, htp]) (by linarith [htp])
    set u : ℝ := c ^ k1 * q ^ j1 with hu_def
    have huI : M < u ∧ u < M + t / 2 := by
      rw [abs_lt] at hu
      constructor <;> linarith [hu]
    obtain ⟨k2, j2, hu'⟩ := bq_dense_pow_mul_pow c q hc1 hq0 hq1 Hrel
      (M + 3 * t / 4) (t / 4) (by linarith [hM1, htp]) (by linarith [htp])
    set u' : ℝ := c ^ k2 * q ^ j2 with hu'_def
    have hu'I : M + t / 2 < u' ∧ u' < M + t := by
      rw [abs_lt] at hu'
      constructor <;> linarith [hu']
    have hPu : ∀ x y, dist x y = u → dist (f x) (f y) = u :=
      step3 j1 k1 (by linarith [huI.1, hM1])
    have hPu' : ∀ x y, dist x y = u' → dist (f x) (f y) = u' :=
      step3 j2 k2 (by linarith [hu'I.1, hM1])
    have hlo : |u - u'| ≤ dist x y := by
      rw [abs_le]
      constructor <;> linarith [huI, hu'I, ht_def, htp]
    have hhi : dist x y ≤ u + u' := by
      have : M < u + u' := by linarith [huI.1, hu'I.1]
      linarith [this, hMt, ht_def]
    obtain ⟨z, hzx, hzy⟩ := bq_sphere_inter_nonempty hn2 u u'
      (by linarith [huI.1, hM1]) (by linarith [hu'I.1, hM1]) x y hlo hhi
    have h1 := hPu x z hzx
    have h2 := hPu' y z hzy
    rw [← hfeq] at h2
    linarith [h1, h2, huI, hu'I]
  -- Step 5: full induction via injectivity
  have key : ∀ j k, ∀ x y, dist x y = c ^ k * q ^ j →
      dist (f x) (f y) = c ^ k * q ^ j := by
    intro j
    induction j with
    | zero =>
      intro k x y hxy
      simp only [pow_zero, mul_one] at hxy ⊢
      exact step1 k x y hxy
    | succ j ih =>
      intro k x y hxy
      have hposd : (0 : ℝ) < c ^ k * q ^ j :=
        mul_pos (pow_pos hc0 _) (pow_pos hq0 _)
      have hPd := ih k
      have hPcd : ∀ x y, dist x y = c * (c ^ k * q ^ j) →
          dist (f x) (f y) = c * (c ^ k * q ^ j) := by
        have h := ih (k + 1)
        have e : c ^ (k + 1) * q ^ j = c * (c ^ k * q ^ j) := by
          rw [pow_succ']
          ring
        rwa [e] at h
      have hw := step2 (c ^ k * q ^ j) hposd hPd hPcd
      have e3 : c ^ k * q ^ (j + 1) = q * (c ^ k * q ^ j) := by
        rw [pow_succ]
        ring
      rw [e3] at hxy
      rcases hw x y hxy with h | h
      · rw [← e3] at h
        exact h
      · exfalso
        have hxy0 : x = y := hinj h
        rw [hxy0, dist_self] at hxy
        have hpos2 : (0 : ℝ) < q * (c ^ k * q ^ j) := mul_pos hq0 hposd
        -- hxy : 0 = q*d, but q*d > 0
        linarith [hxy, hpos2]
  intro k j x y hxy
  exact key j k x y hxy

/-- Scale step for `Fin 2`: weak preservation plus a helper upgrades to preservation.
    Packages `bq_wpres_of_regular_simplex` with `bq_pres_of_wpres` for `n = 2`,
    where the simplex relation simplifies to `t ^ 2 = 4 * r ^ 2 - s ^ 2`. -/
private theorem bq_pres_scale_step_fin2
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (r s t e : ℝ) (hs : 0 < s) (ht : 0 < t) (hr : 0 < r)
    (hformula : t ^ 2 = 4 * r ^ 2 - s ^ 2)
    (he : 0 < e) (hle : e ≤ 2 * t) (hne : e ≠ t)
    (hPr : ∀ x y, dist x y = r → dist (f x) (f y) = r)
    (hPs : ∀ x y, dist x y = s → dist (f x) (f y) = s)
    (hPe : ∀ x y, dist x y = e → dist (f x) (f y) = e) :
    ∀ x y, dist x y = t → dist (f x) (f y) = t := by
  have hn2 : (2 : ℕ) ≤ 2 := by norm_num
  apply bq_pres_of_wpres hn2 f t e he hle hne _ hPe
  intro x y hxy
  apply bq_wpres_of_regular_simplex hn2 f r s t hs ht hr _ hPr hPs x y hxy
  have h2 : ((((2 : ℕ)) : ℝ) - 1) / (((2 : ℕ)) : ℝ) = 1 / 2 := by norm_num
  have hmid : 4 * r ^ 2 - 2 * s ^ 2 * ((((2 : ℕ)) : ℝ) - 1) / (((2 : ℕ)) : ℝ)
      = 4 * r ^ 2 - s ^ 2 := by
    rw [mul_div_assoc, h2]
    ring
  rw [hmid]
  exact hformula

/-- Growth by `√3` on the plane, from `bq_pres_mul_c` with `n = 2`. -/
private theorem bq_pres_mul_sqrt3_fin2
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (e : ℝ) (he : 0 < e)
    (h : ∀ x y, dist x y = e → dist (f x) (f y) = e) :
    ∀ x y, dist x y = Real.sqrt 3 * e → dist (f x) (f y) = Real.sqrt 3 * e := by
  have hn2 : (2 : ℕ) ≤ 2 := by norm_num
  have hstep := bq_pres_mul_c hn2 f e he h
  have hc : Real.sqrt (2 * ((((2 : ℕ)) : ℝ) + 1) / ((((2 : ℕ)) : ℝ))) = Real.sqrt 3 := by
    congr 1
    norm_num
  rwa [hc] at hstep

/-- All `√(11/3)^k (1/√3)^j` preserved on the plane. -/
private theorem bq_pres_pow_of_eq_two
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hf : ∀ x y, dist x y = 1 → dist (f x) (f y) = 1) :
    ∀ k j : ℕ, ∀ x y,
      dist x y = (Real.sqrt (11 / 3)) ^ k * (1 / Real.sqrt 3) ^ j →
      dist (f x) (f y) = (Real.sqrt (11 / 3)) ^ k * (1 / Real.sqrt 3) ^ j := by
  set A : ℝ := Real.sqrt (11 / 3) with hA_def
  set B : ℝ := 1 / Real.sqrt 3 with hB_def
  have h3pos : (0 : ℝ) < 3 := by norm_num
  have h3nn : (0 : ℝ) ≤ 3 := le_of_lt h3pos
  have hsqrt3pos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr h3pos
  have hsqrt3ne : Real.sqrt 3 ≠ 0 := ne_of_gt hsqrt3pos
  have hsqrt3sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt h3nn
  have hApos : (0 : ℝ) < A := by
    rw [hA_def]
    exact Real.sqrt_pos.mpr (by norm_num)
  have hAsq : A ^ 2 = 11 / 3 := by
    rw [hA_def]
    exact Real.sq_sqrt (by norm_num)
  have hA1 : (1 : ℝ) < A := by
    rw [hA_def, ← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hBpos : (0 : ℝ) < B := by
    rw [hB_def]
    positivity
  have hBlt1 : B < 1 := by
    have h13 : (1 : ℝ) < Real.sqrt 3 := by
      conv_lhs => rw [← Real.sqrt_one]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rw [hB_def]
    exact (div_lt_one hsqrt3pos).mpr h13
  have hBsq : B ^ 2 = 1 / 3 := by
    rw [hB_def, div_pow, one_pow, hsqrt3sq]
  -- Step (ii): growth by √(11/3) via the asymmetric kite
  have stepA : ∀ d : ℝ, 0 < d → (∀ x y, dist x y = d → dist (f x) (f y) = d) →
      ∀ x y, dist x y = A * d → dist (f x) (f y) = A * d := by
    intro d hd hPd
    have hPsqrt := bq_pres_mul_sqrt3_fin2 f d hd hPd
    have hle : d ≤ 2 * (A * d) := by
      have h12 : (1 : ℝ) ≤ 2 * A := by linarith [hA1]
      have h := (le_mul_iff_one_le_right hd).mpr h12
      linarith [h]
    have hne : d ≠ A * d := by
      intro hcon
      have hA1' : A = 1 := by
        have h1 : A * d = 1 * d := by rw [one_mul]; exact hcon.symm
        exact mul_right_cancel₀ (ne_of_gt hd) h1
      linarith [hA1]
    have hw : ∀ x y, dist x y = A * d →
        dist (f x) (f y) = A * d ∨ f x = f y := by
      intro x y hxy_t
      have htpos : (0 : ℝ) < A * d := mul_pos hApos hd
      have hne_xy : x ≠ y := by
        intro hcon
        rw [hcon, dist_self] at hxy_t
        linarith
      set σ : ℝ := -d / (2 * Real.sqrt 3) with hσ_def
      set τ : ℝ := 5 * d / (2 * Real.sqrt 3) with hτ_def
      obtain ⟨p, q, hpq_dist, hxp, hyp, hxq, hyq⟩ :=
        bq_exists_kite_config (by norm_num : 2 ≤ 2) x y hne_xy σ τ
      have hAsq_d : (A * d) ^ 2 / 4 = 11 * d ^ 2 / 12 := by
        rw [mul_pow, hAsq]; ring
      have hσsq : σ ^ 2 = d ^ 2 / 12 := by
        rw [hσ_def, div_pow, mul_pow, hsqrt3sq]; ring
      have hτsq : τ ^ 2 = 25 * d ^ 2 / 12 := by
        rw [hτ_def, div_pow, mul_pow, mul_pow, hsqrt3sq]; ring
      have hsqrt3d : (Real.sqrt 3 * d) ^ 2 = 3 * d ^ 2 := by
        rw [mul_pow, hsqrt3sq]
      rw [hxy_t, hAsq_d, hσsq] at hxp
      rw [hxy_t, hAsq_d, hσsq] at hyp
      rw [hxy_t, hAsq_d, hτsq] at hxq
      rw [hxy_t, hAsq_d, hτsq] at hyq
      have hxp_d : dist x p = d := by
        have h2 : dist x p ^ 2 = d ^ 2 := by linarith [hxp]
        exact (pow_left_inj₀ dist_nonneg hd.le two_ne_zero).mp h2
      have hyp_d : dist y p = d := by
        have h2 : dist y p ^ 2 = d ^ 2 := by linarith [hyp]
        exact (pow_left_inj₀ dist_nonneg hd.le two_ne_zero).mp h2
      have hxq_d : dist x q = Real.sqrt 3 * d := by
        have h2 : dist x q ^ 2 = (Real.sqrt 3 * d) ^ 2 := by
          rw [hsqrt3d]; linarith [hxq]
        have hnn : (0 : ℝ) ≤ Real.sqrt 3 * d :=
          mul_nonneg (Real.sqrt_nonneg _) hd.le
        exact (pow_left_inj₀ dist_nonneg hnn two_ne_zero).mp h2
      have hyq_d : dist y q = Real.sqrt 3 * d := by
        have h2 : dist y q ^ 2 = (Real.sqrt 3 * d) ^ 2 := by
          rw [hsqrt3d]; linarith [hyq]
        have hnn : (0 : ℝ) ≤ Real.sqrt 3 * d :=
          mul_nonneg (Real.sqrt_nonneg _) hd.le
        exact (pow_left_inj₀ dist_nonneg hnn two_ne_zero).mp h2
      have hdiff : σ - τ = -(Real.sqrt 3 * d) := by
        have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt h3nn
        have h2s : (2 : ℝ) * Real.sqrt 3 ≠ 0 :=
          mul_ne_zero (by norm_num) hsqrt3ne
        rw [hσ_def, hτ_def, ← sub_div, div_eq_iff h2s]
        linear_combination 2 * d * h3
      have hστ : |σ - τ| = Real.sqrt 3 * d := by
        rw [hdiff, abs_neg, abs_of_pos (mul_pos hsqrt3pos hd)]
      have hpq_sqrt : dist p q = Real.sqrt 3 * d := by
        rw [hpq_dist, hστ]
      have hfpq : f p ≠ f q := by
        have h1 := hPsqrt p q hpq_sqrt
        intro hcon
        rw [hcon, dist_self] at h1
        have hpos : (0 : ℝ) < Real.sqrt 3 * d := mul_pos hsqrt3pos hd
        linarith
      have himg1 : dist (f x) (f p) = dist (f y) (f p) := by
        rw [hPd x p hxp_d, hPd y p hyp_d]
      have himg2 : dist (f x) (f q) = dist (f y) (f q) := by
        rw [hPsqrt x q hxq_d, hPsqrt y q hyq_d]
      have hN5 := bq_planar_kite_dichotomy (f p) (f q) (f x) (f y) hfpq himg1 himg2
      rcases hN5 with h | h
      · exact Or.inr h
      · left
        have e1 : dist (f x) (f p) = d := hPd x p hxp_d
        have e2 : dist (f x) (f q) = Real.sqrt 3 * d := hPsqrt x q hxq_d
        have e3 : dist (f p) (f q) = Real.sqrt 3 * d := hPsqrt p q hpq_sqrt
        rw [e1, e2, e3, hsqrt3d] at h
        have hX : d ^ 2 - 3 * d ^ 2 + 3 * d ^ 2 = d ^ 2 := by ring
        rw [hX] at h
        have hdne : d ≠ 0 := ne_of_gt hd
        have h3d : (3 : ℝ) * d ^ 2 ≠ 0 :=
          mul_ne_zero (by norm_num) (pow_ne_zero 2 hdne)
        have hY : (d ^ 2) ^ 2 / (3 * d ^ 2) = d ^ 2 / 3 := by
          field_simp
        rw [hY] at h
        have ht2 : dist (f x) (f y) ^ 2 = (A * d) ^ 2 := by
          have eA : (A * d) ^ 2 = 11 * d ^ 2 / 3 := by
            rw [mul_pow, hAsq]; ring
          rw [eA]; linarith [h]
        exact (pow_left_inj₀ dist_nonneg htpos.le two_ne_zero).mp ht2
    intro x y hxy_t
    exact bq_pres_of_wpres (by norm_num) f (A * d) d hd hle hne hw hPd x y hxy_t
  -- Step (iii): shrinking by √3 via the simplex step
  have stepB : ∀ d : ℝ, 0 < d → (∀ x y, dist x y = d → dist (f x) (f y) = d) →
      ∀ x y, dist x y = B * d → dist (f x) (f y) = B * d := by
    intro d hd hPd
    have hAd : (0 : ℝ) < A * d := mul_pos hApos hd
    have hBd : (0 : ℝ) < B * d := mul_pos hBpos hd
    have hPAd := stepA d hd hPd
    have hformula : (B * d) ^ 2 = 4 * d ^ 2 - (A * d) ^ 2 := by
      have e1 : (B * d) ^ 2 = (1 / 3) * d ^ 2 := by rw [mul_pow, hBsq]
      have e2 : (A * d) ^ 2 = (11 / 3) * d ^ 2 := by rw [mul_pow, hAsq]
      rw [e1, e2]; ring
    have hle : d ≤ 2 * (B * d) := by
      have h32 : Real.sqrt 3 ≤ 2 := by
        have h4 : (2 : ℝ) = Real.sqrt (2 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
        rw [h4]
        exact Real.sqrt_le_sqrt (by norm_num)
      have hB2 : (1 : ℝ) ≤ 2 * B := by
        have e : (2 : ℝ) * B = 2 / Real.sqrt 3 := by rw [hB_def]; ring
        rw [e, le_div_iff₀ hsqrt3pos, one_mul]
        exact h32
      have h := (le_mul_iff_one_le_right hd).mpr hB2
      linarith [h]
    have hne : d ≠ B * d := by
      intro hcon
      have hB1' : B = 1 := by
        have h1 : B * d = 1 * d := by rw [one_mul]; exact hcon.symm
        exact mul_right_cancel₀ (ne_of_gt hd) h1
      linarith [hBlt1]
    exact bq_pres_scale_step_fin2 f d (A * d) (B * d) d
      hAd hBd hd hformula hd hle hne hPd hPAd hPd
  -- Double induction on k (stepA) and j (stepB)
  have stepA' : ∀ e : ℝ, 0 < e → (∀ x y, dist x y = e → dist (f x) (f y) = e) →
      ∀ m : ℕ, ∀ x y, dist x y = A ^ m * e → dist (f x) (f y) = A ^ m * e := by
    intro e he hPe m
    induction m with
    | zero =>
      intro x y hxy
      simp only [pow_zero, one_mul] at hxy ⊢
      exact hPe x y hxy
    | succ m ih =>
      intro x y hxy
      have hpos : (0 : ℝ) < A ^ m * e := mul_pos (pow_pos hApos _) he
      have hstep := stepA (A ^ m * e) hpos ih
      have heq : A ^ (m + 1) * e = A * (A ^ m * e) := by rw [pow_succ']; ring
      rw [heq] at hxy ⊢
      exact hstep x y hxy
  have key : ∀ j k : ℕ, ∀ x y, dist x y = A ^ k * B ^ j →
      dist (f x) (f y) = A ^ k * B ^ j := by
    intro j
    induction j with
    | zero =>
      intro k x y hxy
      simp only [pow_zero, mul_one] at hxy ⊢
      have h := stepA' 1 zero_lt_one hf k x y
      simp only [mul_one] at h
      exact h hxy
    | succ j ih =>
      intro k x y hxy
      have hpos : (0 : ℝ) < A ^ k * B ^ j :=
        mul_pos (pow_pos hApos _) (pow_pos hBpos _)
      have hstep := stepB (A ^ k * B ^ j) hpos (ih k)
      have heq : A ^ k * B ^ (j + 1) = B * (A ^ k * B ^ j) := by
        rw [pow_succ]; ring
      rw [heq] at hxy ⊢
      exact hstep x y hxy
  intro k j x y hxy
  exact key j k x y hxy

/-- Squared norm of an orthonormal combination. -/
private theorem bq_norm_pair {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (e1 e2 : V) (he1 : ‖e1‖ = 1) (he2 : ‖e2‖ = 1) (hortho : ⟪e1, e2⟫_ℝ = 0)
    (a b : ℝ) : ‖a • e1 + b • e2‖ ^ 2 = a ^ 2 + b ^ 2 := by
  have horth : ⟪a • e1, b • e2⟫_ℝ = 0 := by
    rw [real_inner_smul_left, real_inner_smul_right, hortho, mul_zero, mul_zero]
  have hexp := norm_add_sq_real (a • e1) (b • e2)
  rw [horth, mul_zero, add_zero] at hexp
  have h1 : ‖a • e1‖ ^ 2 = a ^ 2 := by
    rw [norm_smul, he1, mul_one, Real.norm_eq_abs, sq_abs]
  have h2 : ‖b • e2‖ ^ 2 = b ^ 2 := by
    rw [norm_smul, he2, mul_one, Real.norm_eq_abs, sq_abs]
  rw [h1, h2] at hexp
  exact hexp

/-- Orthonormal expansion in the Euclidean plane. -/
private theorem bq_basis_expand_fin2 (e1 e2 : EuclideanSpace ℝ (Fin 2))
    (he1 : ‖e1‖ = 1) (he2 : ‖e2‖ = 1) (hortho : ⟪e1, e2⟫_ℝ = 0)
    (w : EuclideanSpace ℝ (Fin 2)) :
    w = ⟪w, e1⟫_ℝ • e1 + ⟪w, e2⟫_ℝ • e2 := by
  set z : EuclideanSpace ℝ (Fin 2)
    := w - (⟪w, e1⟫_ℝ • e1 + ⟪w, e2⟫_ℝ • e2) with hz
  have hsym : ⟪e2, e1⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact hortho
  have hz1 : ⟪z, e1⟫_ℝ = 0 := by
    rw [hz, inner_sub_left, inner_add_left, real_inner_smul_left,
      real_inner_smul_left, real_inner_self_eq_norm_sq, he1, hsym]
    ring
  have hz2 : ⟪z, e2⟫_ℝ = 0 := by
    rw [hz, inner_sub_left, inner_add_left, real_inner_smul_left,
      real_inner_smul_left, hortho, real_inner_self_eq_norm_sq, he2]
    ring
  have horth : Orthonormal ℝ (fun i : Fin 2 => ![e1, e2] i) := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [he1, he2, hortho, hsym]
  have hindep := horth.linearIndependent
  have hspan : Submodule.span ℝ (Set.range (fun i : Fin 2 => ![e1, e2] i)) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hindep]
    rw [finrank_euclideanSpace_fin]
    simp [Fintype.card_fin]
  have hzmem : z ∈ (Submodule.span ℝ (Set.range (fun i : Fin 2 => ![e1, e2] i)))ᗮ := by
    rw [Submodule.mem_orthogonal']
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      fin_cases k <;> simp [hz1, hz2]
    | zero => simp
    | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
    | smul a x _ hx => rw [inner_smul_right, hx, mul_zero]
  rw [hspan] at hzmem
  have hmem : z ∈ (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin 2))) := Submodule.mem_top
  have hzself : ⟪z, z⟫_ℝ = 0 :=
    Submodule.inner_right_of_mem_orthogonal hmem hzmem
  have hnorm : ‖z‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq]
    exact hzself
  have hznorm : ‖z‖ = 0 := by nlinarith [hnorm, norm_nonneg z]
  have hz0 : z = 0 := norm_eq_zero.mp hznorm
  have hzz : w - (⟪w, e1⟫_ℝ • e1 + ⟪w, e2⟫_ℝ • e2) = 0 := hz0
  have := congrArg (· + (⟪w, e1⟫_ℝ • e1 + ⟪w, e2⟫_ℝ • e2)) hzz
  simpa using this

/-- A vector orthogonal to `e1` is parallel to `e2` in the Euclidean plane. -/
private theorem bq_ortho_parallel_fin2 (e1 e2 : EuclideanSpace ℝ (Fin 2))
    (he1 : ‖e1‖ = 1) (he2 : ‖e2‖ = 1) (hortho : ⟪e1, e2⟫_ℝ = 0)
    (w : EuclideanSpace ℝ (Fin 2)) (hw : ⟪w, e1⟫_ℝ = 0) :
    ∃ t : ℝ, w = t • e2 := by
  refine ⟨⟪w, e2⟫_ℝ, ?_⟩
  have hexp := bq_basis_expand_fin2 e1 e2 he1 he2 hortho w
  rw [hw, zero_smul, zero_add] at hexp
  exact hexp

/-- Density of preserved distances. -/
private theorem bq_dense_nonneg_preserved {n : ℕ} (hn : 2 ≤ n)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf : ∀ x y : EuclideanSpace ℝ (Fin n), dist x y = 1 → dist (f x) (f y) = 1) :
    ∀ t : ℝ, 0 ≤ t →
      t ∈ closure {s : ℝ | 0 ≤ s ∧ ∀ x y, dist x y = s → dist (f x) (f y) = s} := by
  -- general closure argument from density of `A^k B^j` values
  have closure_of_dense : ∀ (A B : ℝ), 1 < A → 0 < B → B < 1 →
      (∀ k j : ℕ, A ^ k * B ^ j = 1 → k = 0 ∧ j = 0) →
      (∀ k j : ℕ, ∀ x y, dist x y = A ^ k * B ^ j →
        dist (f x) (f y) = A ^ k * B ^ j) →
      ∀ t : ℝ, 0 ≤ t →
        t ∈ closure
          {s : ℝ | 0 ≤ s ∧ ∀ x y, dist x y = s → dist (f x) (f y) = s} := by
    intro A B hA hB0 hB1 Hrel hpres t ht
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hnn : ∀ k j : ℕ, (0 : ℝ) ≤ A ^ k * B ^ j :=
      fun k j => mul_nonneg (pow_nonneg (le_of_lt (lt_trans zero_lt_one hA)) _)
        (pow_nonneg hB0.le _)
    rcases eq_or_lt_of_le ht with h0 | hpos
    · -- target `0`: find a small positive preserved value
      subst h0
      obtain ⟨k, j, hkj⟩ := bq_dense_pow_mul_pow A B hA hB0 hB1 Hrel
        (ε / 2) (ε / 2) (by linarith) (by linarith)
      refine ⟨A ^ k * B ^ j, ⟨hnn k j, hpres k j⟩, ?_⟩
      have h2 := abs_lt.mp hkj
      have hpos2 : (0 : ℝ) < A ^ k * B ^ j := by linarith [h2.1]
      rw [Real.dist_eq, zero_sub, abs_neg, abs_of_pos hpos2]
      linarith [h2.2]
    · -- positive target: approximate directly
      obtain ⟨k, j, hkj⟩ := bq_dense_pow_mul_pow A B hA hB0 hB1 Hrel
        t ε hpos hε
      refine ⟨A ^ k * B ^ j, ⟨hnn k j, hpres k j⟩, ?_⟩
      rw [Real.dist_eq, abs_sub_comm]
      exact hkj
  rcases eq_or_lt_of_le hn with h | h
  · -- `n = 2`: the asymmetric kite values
    subst h
    have hA : (1 : ℝ) < Real.sqrt (11 / 3) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have hB0 : (0 : ℝ) < 1 / Real.sqrt 3 := by positivity
    have hB1 : (1 / Real.sqrt 3 : ℝ) < 1 := by
      have h13 : (1 : ℝ) < Real.sqrt 3 := by
        conv_lhs => rw [← Real.sqrt_one]
        exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      exact (div_lt_one (Real.sqrt_pos.mpr (by norm_num))).mpr h13
    have hpres := bq_pres_pow_of_eq_two f hf
    exact closure_of_dense _ _ hA hB0 hB1
      (fun k j h => bq_no_unit_relation_kite k j h) hpres
  · -- `3 ≤ n`: the simplex values
    have hn3 : 3 ≤ n := by omega
    obtain ⟨hc1, hq0, hq1⟩ := bq_cq_bounds hn3
    have hpres := bq_pres_pow_of_three_le hn3 f hf
    exact closure_of_dense _ _ hc1 hq0 hq1
      (fun k j h => bq_no_unit_relation_simplex hn3 k j h) hpres

section
namespace MathlibExt.Geometry.Euclidean.BeckmanQuarlesWanted

/--
**Beckman–Quarles theorem.** Let $n \ge 2$ and let $f : \mathbb{R}^n \to \mathbb{R}^n$ be a map of
$n$-dimensional real Euclidean space such that $\lVert f(x) - f(y) \rVert = 1$ whenever
$\lVert x - y \rVert = 1$. Then $f$ is an isometry, that is,
$\lVert f(x) - f(y) \rVert = \lVert x - y \rVert$ for all $x, y \in \mathbb{R}^n$.

Surjectivity of $f$ is neither assumed nor concluded.

Source: F. S. Beckman and D. A. Quarles Jr., On isometries of Euclidean spaces, Proc. Amer. Math.
Soc. 4 (1953) 810–815 original theorem; standard formulation for `ℝ^n, n ≥ 2`.

Proves `Wanted` entry `beckman_quarles`.
-/
theorem beckman_quarles
    {n : ℕ} (hn : 2 ≤ n)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf : ∀ x y : EuclideanSpace ℝ (Fin n), dist x y = 1 → dist (f x) (f y) = 1) :
    Isometry f := by
  have hdense := bq_dense_nonneg_preserved hn f hf
  have hsmall : ∀ ε > 0, ∃ s, 0 < s ∧ s < ε ∧
      ∀ x y, dist x y = s → dist (f x) (f y) = s := by
    intro ε hε
    have hhalf : (0 : ℝ) < ε / 2 := by linarith
    have hmem := hdense (ε / 2) (le_of_lt hhalf)
    rw [Metric.mem_closure_iff] at hmem
    obtain ⟨s, hs, hclose⟩ := hmem (ε / 2) hhalf
    refine ⟨s, ?_, ?_, hs.2⟩
    · rcases eq_or_lt_of_le hs.1 with h0 | hpos
      · exfalso
        rw [← h0, Real.dist_eq, sub_zero, abs_of_pos hhalf] at hclose
        linarith [hclose]
      · exact hpos
    · rw [Real.dist_eq] at hclose
      have h2 := (abs_lt.mp hclose).1
      linarith [h2]
  exact bq_isometry_of_dense_preserved f
    (bq_continuous_of_small_preserved hn f hsmall) hdense

end MathlibExt.Geometry.Euclidean.BeckmanQuarlesWanted
end
