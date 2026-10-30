/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import MathlibExt.Topology.MetricSpace.PointedGromovHausdorff
import Mathlib.Analysis.Normed.Group.Basic

/-! Focused positive tests for pointed Gromov–Hausdorff convergence. -/

namespace PointedGromovHausdorffTests

def twoPt (a : ℝ) : Set ℝ := {0, a}

def pt0 (a : ℝ) : ↥(twoPt a) := ⟨0, by simp [twoPt]⟩

theorem T1_general (a : ℕ → ℝ) (R : ℝ) (hpos : ∀ k, 0 < a k) (hR : 0 < R)
    (hlim : ∀ ε > 0, ∀ᶠ k in Filter.atTop, dist (a k) R < ε) :
    GromovHausdorff.PointedGHConverges (X := fun k => ↥(twoPt (a k)))
      (fun k => pt0 (a k)) (⟨0, by simp [twoPt]⟩ : ↥(twoPt R)) := by
  classical
  intro R' hR' ε hε
  filter_upwards [hlim ε hε] with k hk
  have hposk : 0 < a k := hpos k
  have hne : a k ≠ 0 := by linarith
  have hdistAR : dist (a k) R = |a k - R| := Real.dist_eq _ _
  have hkabs : |a k - R| < ε := by linarith [hk, hdistAR]
  set f : ↥(Metric.ball (pt0 (a k)) R') → ↥(twoPt R) :=
    fun x => if x.val.val = 0 then (⟨0, by simp [twoPt]⟩ : ↥(twoPt R))
      else (⟨R, by simp [twoPt]⟩ : ↥(twoPt R)) with hf_def
  refine ⟨f, ?_, ?_, ?_⟩
  · have hmem : pt0 (a k) ∈ Metric.ball (pt0 (a k)) R' :=
      Metric.mem_ball_self hR'
    have hcond : ((pt0 (a k) : ↥(twoPt (a k))) : ℝ) = 0 := rfl
    simp [hf_def, hcond]
  · intro x y
    have hxy : dist x y = |x.val.val - y.val.val| := by
      have h1 : dist x y = dist x.val y.val := Subtype.dist_eq _ _
      have h2 : dist x.val y.val = dist x.val.val y.val.val :=
        Subtype.dist_eq _ _
      rw [h1, h2, Real.dist_eq]
    have hxmem : x.val.val = 0 ∨ x.val.val = a k := by
      have h := x.val.property
      simp only [twoPt, Set.mem_insert_iff, Set.mem_singleton_iff] at h
      exact h
    have hymem : y.val.val = 0 ∨ y.val.val = a k := by
      have h := y.val.property
      simp only [twoPt, Set.mem_insert_iff, Set.mem_singleton_iff] at h
      exact h
    have hbound : |R - a k| ≤ ε := by
      have hcomm : |R - a k| = |a k - R| := abs_sub_comm _ _
      linarith [hkabs, hcomm]
    rcases hxmem with hx0 | hxa <;> rcases hymem with hy0 | hya
    · have hfx : f x = (⟨0, by simp [twoPt]⟩ : ↥(twoPt R)) := by
        simp [hf_def, hx0]
      have hfy : f y = (⟨0, by simp [twoPt]⟩ : ↥(twoPt R)) := by
        simp [hf_def, hy0]
      have hdf : dist (f x) (f y) = 0 := by
        rw [hfx, hfy, Subtype.dist_eq, Real.dist_eq, sub_self, abs_zero]
      have hdxv : dist x.val y.val = 0 := by
        rw [Subtype.dist_eq, Real.dist_eq, hx0, hy0, sub_self, abs_zero]
      rw [hdf, hdxv, sub_self, abs_zero]
      exact hε.le
    · have hfx : f x = (⟨0, by simp [twoPt]⟩ : ↥(twoPt R)) := by
        simp [hf_def, hx0]
      have hfy : f y = (⟨R, by simp [twoPt]⟩ : ↥(twoPt R)) := by
        simp [hf_def, hya, hne]
      have hdf : dist (f x) (f y) = R := by
        rw [hfx, hfy, Subtype.dist_eq, Real.dist_eq, zero_sub, abs_neg,
          abs_of_nonneg hR.le]
      have hdxv : dist x.val y.val = a k := by
        rw [Subtype.dist_eq, Real.dist_eq, hx0, hya, zero_sub, abs_neg,
          abs_of_nonneg hposk.le]
      rw [hdf, hdxv]
      exact hbound
    · have hfx : f x = (⟨R, by simp [twoPt]⟩ : ↥(twoPt R)) := by
        simp [hf_def, hxa, hne]
      have hfy : f y = (⟨0, by simp [twoPt]⟩ : ↥(twoPt R)) := by
        simp [hf_def, hy0]
      have hdf : dist (f x) (f y) = R := by
        rw [hfx, hfy, Subtype.dist_eq, Real.dist_eq, sub_zero,
          abs_of_nonneg hR.le]
      have hdxv : dist x.val y.val = a k := by
        rw [Subtype.dist_eq, Real.dist_eq, hxa, hy0, sub_zero,
          abs_of_nonneg hposk.le]
      rw [hdf, hdxv]
      exact hbound
    · have hfx : f x = (⟨R, by simp [twoPt]⟩ : ↥(twoPt R)) := by
        simp [hf_def, hxa, hne]
      have hfy : f y = (⟨R, by simp [twoPt]⟩ : ↥(twoPt R)) := by
        simp [hf_def, hya, hne]
      have hdf : dist (f x) (f y) = 0 := by
        rw [hfx, hfy, Subtype.dist_eq, Real.dist_eq, sub_self, abs_zero]
      have hdxv : dist x.val y.val = 0 := by
        rw [Subtype.dist_eq, Real.dist_eq, hxa, hya, sub_self, abs_zero]
      rw [hdf, hdxv, sub_self, abs_zero]
      exact hε.le
  · intro z hz
    have hzmem : z.val = 0 ∨ z.val = R := by
      have h := z.property
      simp only [twoPt, Set.mem_insert_iff, Set.mem_singleton_iff] at h
      exact h
    have hzball : dist z (⟨0, by simp [twoPt]⟩ : ↥(twoPt R)) < R' - ε :=
      Metric.mem_ball.mp hz
    have hmem0 : pt0 (a k) ∈ Metric.ball (pt0 (a k)) R' :=
      Metric.mem_ball_self hR'
    rcases hzmem with hz0 | hzR
    · rw [Metric.mem_thickening_iff]
      refine ⟨f ⟨pt0 (a k), hmem0⟩, ⟨⟨pt0 (a k), hmem0⟩, rfl⟩, ?_⟩
      have hcond0 : ((pt0 (a k) : ↥(twoPt (a k))) : ℝ) = 0 := rfl
      have hfz : f ⟨pt0 (a k), hmem0⟩ =
          (⟨0, by simp [twoPt]⟩ : ↥(twoPt R)) := by
        simp [hf_def, hcond0]
      have hdz : dist z (f ⟨pt0 (a k), hmem0⟩) = 0 := by
        rw [hfz]
        have h1 : dist z (⟨0, by simp [twoPt]⟩ : ↥(twoPt R)) =
            dist z.val (0 : ℝ) := Subtype.dist_eq _ _
        rw [h1, Real.dist_eq, hz0, sub_self, abs_zero]
      linarith [hdz, hε]
    · have hdist_zq : dist z (⟨0, by simp [twoPt]⟩ : ↥(twoPt R)) =
          |z.val - 0| := by
        have h1 : dist z (⟨0, by simp [twoPt]⟩ : ↥(twoPt R)) =
            dist z.val (0 : ℝ) := Subtype.dist_eq _ _
        rw [h1, Real.dist_eq]
      have hRR : |R - 0| = R := by
        rw [sub_zero, abs_of_nonneg hR.le]
      have hRlt : R < R' - ε := by
        rw [hzR] at hdist_zq
        linarith [hzball, hdist_zq, hRR]
      have haklt : a k < R' := by
        rcases le_total (a k) R with hle | hle
        · linarith [hRlt, hε]
        · have h1 : 0 ≤ a k - R := by linarith
          have e1 : |a k - R| = a k - R := abs_of_nonneg h1
          linarith [hkabs, hRlt, e1, hε]
      have hmemA : (⟨a k, by simp [twoPt]⟩ : ↥(twoPt (a k))) ∈
          Metric.ball (pt0 (a k)) R' := by
        rw [Metric.mem_ball]
        have h1 : dist (⟨a k, by simp [twoPt]⟩ : ↥(twoPt (a k)))
            (pt0 (a k)) = |a k - 0| := by
          have h11 : dist (⟨a k, by simp [twoPt]⟩ : ↥(twoPt (a k)))
              (pt0 (a k)) = dist (a k) (0 : ℝ) := Subtype.dist_eq _ _
          rw [h11, Real.dist_eq]
        rw [h1, sub_zero, abs_of_nonneg hposk.le]
        exact haklt
      rw [Metric.mem_thickening_iff]
      have hfz : f ⟨⟨a k, by simp [twoPt]⟩, hmemA⟩ =
          (⟨R, by simp [twoPt]⟩ : ↥(twoPt R)) := by
        simp [hf_def, hne]
      refine ⟨(⟨R, by simp [twoPt]⟩ : ↥(twoPt R)),
        ⟨⟨⟨a k, by simp [twoPt]⟩, hmemA⟩, hfz⟩, ?_⟩
      have hdz : dist z (⟨R, by simp [twoPt]⟩ : ↥(twoPt R)) = 0 := by
        have h1 : dist z (⟨R, by simp [twoPt]⟩ : ↥(twoPt R)) =
            dist z.val (R : ℝ) := Subtype.dist_eq _ _
        rw [h1, Real.dist_eq, hzR, sub_self, abs_zero]
      linarith [hdz, hε]

theorem T2_boundary_crossing (R : ℝ) (hR : 0 < R) :
    GromovHausdorff.PointedGHConverges
      (X := fun k => ↥(twoPt (R + 1 / ((k : ℝ) + 1))))
      (fun k => pt0 _) (⟨0, by simp [twoPt]⟩ : ↥(twoPt R)) := by
  have hpos : ∀ k : ℕ, 0 < R + 1 / ((k : ℝ) + 1) := by
    intro k
    have h1 : 0 < 1 / ((k : ℝ) + 1) := by positivity
    linarith [hR]
  have hlim : ∀ ε > 0, ∀ᶠ (k : ℕ) in Filter.atTop,
      dist (R + 1 / ((k : ℝ) + 1)) R < ε := by
    intro ε hε
    have hT : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
        Filter.atTop (nhds (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hT ε hε
    refine Filter.eventually_atTop.mpr ⟨N, fun (k : ℕ) hk => ?_⟩
    have hk1 : dist (1 / ((k : ℝ) + 1)) (0 : ℝ) < ε := hN k hk
    have hdist : dist (R + 1 / ((k : ℝ) + 1)) R =
        dist (1 / ((k : ℝ) + 1)) (0 : ℝ) := by
      rw [Real.dist_eq, Real.dist_eq]
      simp
    linarith [hk1, hdist]
  exact T1_general _ R hpos hR hlim

theorem T8_dis_lt (R : ℝ) (hR : 0 < R) :
    ∀ (R' : ℝ) (_ : 0 < R') (ε : ℝ) (_ : 0 < ε),
      ∀ᶠ (n : ℕ) in Filter.atTop,
        ∃ f : ↥(Metric.ball (pt0 (R + 1 / ((n : ℝ) + 1))) R') → ↥(twoPt R),
          f ⟨pt0 _, Metric.mem_ball_self ‹0 < R'›⟩ =
              (⟨0, by simp [twoPt]⟩ : ↥(twoPt R)) ∧
            (∃ δ, δ < ε ∧ ∀ x y,
              |dist (f x) (f y) - dist x.val y.val| ≤ δ) ∧
            Metric.ball (⟨0, by simp [twoPt]⟩ : ↥(twoPt R)) (R' - ε) ⊆
              Metric.thickening ε (Set.range f) :=
  (GromovHausdorff.pointedGHConverges_iff_dis_lt _ _).mp
    (T2_boundary_crossing R hR)

theorem T8_mpr (R : ℝ) (hR : 0 < R) :
    GromovHausdorff.PointedGHConverges
      (X := fun k => ↥(twoPt (R + 1 / ((k : ℝ) + 1))))
      (fun k => pt0 _) (⟨0, by simp [twoPt]⟩ : ↥(twoPt R)) :=
  (GromovHausdorff.pointedGHConverges_iff_dis_lt _ _).mpr (T8_dis_lt R hR)

theorem T9_dist (a : ℝ) :
    dist (pt0 a) (⟨a, by simp [twoPt]⟩ : ↥(twoPt a)) = |a| := by
  have h1 : dist (pt0 a) (⟨a, by simp [twoPt]⟩ : ↥(twoPt a)) =
      dist (0 : ℝ) a := Subtype.dist_eq _ _
  rw [h1, Real.dist_eq]
  simp

theorem T9_lt (R : ℝ) (k : ℕ) : R < R + 1 / ((k : ℝ) + 1) := by
  have h : 0 < 1 / ((k : ℝ) + 1) := by positivity
  linarith

end PointedGromovHausdorffTests
