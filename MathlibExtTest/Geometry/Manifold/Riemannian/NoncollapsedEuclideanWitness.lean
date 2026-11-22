/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.MetricSpace.PointedGromovHausdorff
import MathlibExt.Geometry.Manifold.Riemannian.Curvature
import MathlibExt.Geometry.Manifold.Riemannian.Volume
import MathlibExt.Geometry.Manifold.Riemannian.VectorSpace
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.Riemannian.Basic

/-!
Test module: the noncollapsed lower-Ricci hypotheses are satisfied by Euclidean
space with its actual Riemannian volume, via a dimension-dependent constant.
-/

noncomputable section

open MeasureTheory
open Bundle
open scoped Manifold ContDiff

namespace NoncollapsedEuclideanWitnessTests

theorem riemannianVolume_ball_pos (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) {r : ℝ}
    (hr : 0 < r) :
    0 < Manifold.riemannianVolume (𝓡 n) (EuclideanSpace ℝ (Fin n)) (Metric.ball x r) := by
  rw [Manifold.riemannianVolume.eq_1, finrank_euclideanSpace_fin,
    Manifold.normalizedHausdorffMeasure.eq_1, MeasureTheory.Measure.smul_apply]
  refine ENNReal.mul_pos ?_ ?_
  · refine ne_of_gt (ENNReal.div_pos_iff.mpr ⟨?_, ?_⟩)
    · exact ne_of_gt (Metric.measure_ball_pos _ _ one_pos)
    · simp
  · have hlip : LipschitzWith 1 (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)) :=
      PiLp.lipschitzWith_ofLp 2 _
    have hle :=
      LipschitzWith.hausdorffMeasure_image_le hlip (Nat.cast_nonneg n) (Metric.ball x r)
    have hpi : μH[(n : ℝ)] = (volume : Measure (Fin n → ℝ)) := by
      have h := MeasureTheory.hausdorffMeasure_pi_real (ι := Fin n)
      rwa [Fintype.card_fin] at h
    rw [hpi] at hle
    have hK : ((1 : NNReal) : ENNReal) = 1 := by simp
    rw [hK, ENNReal.one_rpow, one_mul] at hle
    have hopen : IsOpen (WithLp.ofLp '' Metric.ball x r) := by
      have hfun : ⇑(PiLp.homeomorph 2 (fun _ : Fin n => ℝ)) = WithLp.ofLp := rfl
      have h : IsOpen (⇑(PiLp.homeomorph 2 (fun _ : Fin n => ℝ)) '' Metric.ball x r) :=
        (Homeomorph.isOpen_image (PiLp.homeomorph 2 (fun _ : Fin n => ℝ))).mpr
          Metric.isOpen_ball
      rwa [hfun] at h
    have hne : (WithLp.ofLp '' Metric.ball x r).Nonempty :=
      Set.image_nonempty.mpr (Metric.nonempty_ball.mpr hr)
    have hvolpos : 0 < (volume : Measure (Fin n → ℝ)) (WithLp.ofLp '' Metric.ball x r) :=
      IsOpen.measure_pos _ hopen hne
    have hμpos : 0 < μH[(n : ℝ)] (Metric.ball x r) := lt_of_lt_of_le hvolpos hle
    exact ne_of_gt hμpos

theorem riemannianVolume_singleton (n : ℕ) (hn : 1 ≤ n) (x : EuclideanSpace ℝ (Fin n)) :
    Manifold.riemannianVolume (𝓡 n) (EuclideanSpace ℝ (Fin n)) {x} = 0 := by
  rw [Manifold.riemannianVolume.eq_1, finrank_euclideanSpace_fin,
    Manifold.normalizedHausdorffMeasure.eq_1, MeasureTheory.Measure.smul_apply]
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hd : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hnpos
  have := MeasureTheory.Measure.nullSingletonClass_hausdorff (EuclideanSpace ℝ (Fin n)) hd
  have h0 : μH[(n : ℝ)] ({x} : Set (EuclideanSpace ℝ (Fin n))) = 0 :=
    Set.Subsingleton.measure_zero (Set.subsingleton_singleton (a := x)) _
  rw [h0, smul_zero]

theorem exists_vol_lower_bound (n : ℕ) :
    ∃ v : ℝ, 0 < v ∧
      ENNReal.ofReal v <
        Manifold.riemannianVolume (𝓡 n) (EuclideanSpace ℝ (Fin n)) (Metric.ball 0 1) := by
  have hpos : 0 < Manifold.riemannianVolume (𝓡 n) (EuclideanSpace ℝ (Fin n))
      (Metric.ball 0 1) :=
    riemannianVolume_ball_pos n 0 one_pos
  obtain ⟨r, _, hr0, hrb⟩ := ENNReal.lt_iff_exists_real_btwn.mp hpos
  exact ⟨r, ENNReal.ofReal_pos.mp hr0, hrb⟩

theorem full_hypothesis_bundle (n : ℕ) :
    ∃ lam v : ℝ, 0 < v ∧
      (∀ _ : ℕ, Manifold.RicciGE (𝓡 n) (EuclideanSpace ℝ (Fin n)) (-lam)) ∧
      (∀ _ : ℕ, ENNReal.ofReal v <
        Manifold.riemannianVolume (𝓡 n) (EuclideanSpace ℝ (Fin n))
          (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) ∧
      GromovHausdorff.PointedGHConverges (X := fun _ : ℕ => EuclideanSpace ℝ (Fin n))
        (fun _ : ℕ => (0 : EuclideanSpace ℝ (Fin n))) (0 : EuclideanSpace ℝ (Fin n)) := by
  obtain ⟨v, hvpos, hvlt⟩ := exists_vol_lower_bound n
  refine ⟨0, v, hvpos, ?_, ?_, ?_⟩
  · intro i
    rw [Manifold.RicciGE.eq_1]
    intro x w
    rw [Manifold.ricci_vectorSpace, neg_zero, zero_mul]
  · intro i
    exact hvlt
  · exact GromovHausdorff.pointedGHConverges_const (0 : EuclideanSpace ℝ (Fin n))

theorem positive_dim_bundle :
    ∃ lam v : ℝ, 0 < v ∧
      (∀ _ : ℕ, Manifold.RicciGE (𝓡 3) (EuclideanSpace ℝ (Fin 3)) (-lam)) ∧
      (∀ _ : ℕ, ENNReal.ofReal v <
        Manifold.riemannianVolume (𝓡 3) (EuclideanSpace ℝ (Fin 3))
          (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1)) ∧
      GromovHausdorff.PointedGHConverges (X := fun _ : ℕ => EuclideanSpace ℝ (Fin 3))
        (fun _ : ℕ => (0 : EuclideanSpace ℝ (Fin 3))) (0 : EuclideanSpace ℝ (Fin 3)) :=
  full_hypothesis_bundle 3

example : CompleteSpace (EuclideanSpace ℝ (Fin 3)) := inferInstance

example : IsManifold (𝓡 3) ∞ (EuclideanSpace ℝ (Fin 3)) := inferInstance

example : IsRiemannianManifold (𝓡 3) (EuclideanSpace ℝ (Fin 3)) := inferInstance

example : BorelSpace (EuclideanSpace ℝ (Fin 3)) := inferInstance

end NoncollapsedEuclideanWitnessTests
