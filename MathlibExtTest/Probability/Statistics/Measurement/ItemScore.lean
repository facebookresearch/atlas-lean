/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Measurement.ItemScore

/-!
# Tests for the canonical 2PL law and score

One Rasch item and a two-item two-slope instance.
-/

@[expose] public section

namespace MathlibExtTest.Probability.Statistics.Measurement.ItemScore

open MeasureTheory MathlibExt.Probability.Statistics
open MathlibExt.Probability.Statistics.Measurement

/-- One Rasch item at `θ = b`: `ι = Fin 1`, `a ≡ 1`, `b ≡ 2`, `θ = 2`,
so `p (θ) = sigmoid 0 = 1 / 2`.  The density is `1 / 2` on both
outcomes, the score is `1 / 2` at `true` and `-1 / 2` at `false`,
and its actual integral is `0`. -/
example :
    ((twoPLPMF (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => (2 : ℝ)) 2
        (fun _ => true)).toReal = 1 / 2)
    ∧ (VectorInference.score
        (fun t Y => (twoPLPMF (fun _ : Fin 1 => (1 : ℝ))
          (fun _ : Fin 1 => (2 : ℝ)) t Y).toReal) 2 (fun _ => true) = 1 / 2)
    ∧ (VectorInference.score
        (fun t Y => (twoPLPMF (fun _ : Fin 1 => (1 : ℝ))
          (fun _ : Fin 1 => (2 : ℝ)) t Y).toReal) 2 (fun _ => false) = -1 / 2)
    ∧ (∫ Y, VectorInference.score
        (fun t Y => (twoPLPMF (fun _ : Fin 1 => (1 : ℝ))
          (fun _ : Fin 1 => (2 : ℝ)) t Y).toReal) 2 Y
        ∂(FisherInformation.lawOf Measure.count
          (fun t Y => (twoPLPMF (fun _ : Fin 1 => (1 : ℝ))
            (fun _ : Fin 1 => (2 : ℝ)) t Y).toReal) 2) = 0) := by
  have e1 : (twoPLPMF (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => (2 : ℝ)) 2
      (fun _ => true)).toReal = 1 / 2 := by
    simp only [twoPLPMF_toReal, Fin.prod_univ_one, ite_true]
    rw [show (1 : ℝ) * (2 - 2) = 0 by norm_num, Real.sigmoid_zero]
    norm_num
  have h2r := (twoPL_score_eq_sum (fun _ : Fin 1 => (1 : ℝ))
    (fun _ : Fin 1 => (2 : ℝ)) 2)
  have e2 : VectorInference.score
      (fun t Y => (twoPLPMF (fun _ : Fin 1 => (1 : ℝ))
        (fun _ : Fin 1 => (2 : ℝ)) t Y).toReal) 2 (fun _ => true) = 1 / 2 := by
    rw [h2r]
    simp only [Fin.sum_univ_one, ite_true]
    rw [show (1 : ℝ) * (2 - 2) = 0 by norm_num, Real.sigmoid_zero]
    norm_num
  have e3 : VectorInference.score
      (fun t Y => (twoPLPMF (fun _ : Fin 1 => (1 : ℝ))
        (fun _ : Fin 1 => (2 : ℝ)) t Y).toReal) 2 (fun _ => false)
      = -1 / 2 := by
    rw [h2r]
    simp only [Fin.sum_univ_one, Bool.false_eq_true, ite_false]
    rw [show (1 : ℝ) * (2 - 2) = 0 by norm_num, Real.sigmoid_zero]
    norm_num
  have e4 : (∫ Y, VectorInference.score
      (fun t Y => (twoPLPMF (fun _ : Fin 1 => (1 : ℝ))
        (fun _ : Fin 1 => (2 : ℝ)) t Y).toReal) 2 Y
      ∂(FisherInformation.lawOf Measure.count
        (fun t Y => (twoPLPMF (fun _ : Fin 1 => (1 : ℝ))
          (fun _ : Fin 1 => (2 : ℝ)) t Y).toReal) 2) = 0) :=
    integral_vector_score_twoPL (fun _ : Fin 1 => (1 : ℝ))
      (fun _ : Fin 1 => (2 : ℝ)) 2
  exact ⟨e1, e2, e3, e4⟩

/-- Two nonidentical slopes, normalized finite density: `ι = Fin 2`,
`a = (1, 2)` (so `a 0 ≠ a 1`), `b ≡ 0`, `θ = 1`.  The `toReal`
density is strictly positive on every pattern, sums to `1` over the
finite outcome space, and the all-true score differs from the
all-false score. -/
example :
    ((fun j : Fin 2 => if j = 0 then (1 : ℝ) else 2) 0
      ≠ (fun j : Fin 2 => if j = 0 then (1 : ℝ) else 2) 1)
    ∧ (∑ Y : Fin 2 → Bool, (twoPLPMF
        (fun j : Fin 2 => if j = 0 then (1 : ℝ) else 2)
        (fun _ : Fin 2 => (0 : ℝ)) 1 Y).toReal = 1)
    ∧ (∀ Y : Fin 2 → Bool, 0 < (twoPLPMF
        (fun j : Fin 2 => if j = 0 then (1 : ℝ) else 2)
        (fun _ : Fin 2 => (0 : ℝ)) 1 Y).toReal)
    ∧ (VectorInference.score
        (fun t Y => (twoPLPMF (fun j : Fin 2 => if j = 0 then (1 : ℝ) else 2)
          (fun _ : Fin 2 => (0 : ℝ)) t Y).toReal) 1 (fun _ => true)
      ≠ VectorInference.score
        (fun t Y => (twoPLPMF (fun j : Fin 2 => if j = 0 then (1 : ℝ) else 2)
          (fun _ : Fin 2 => (0 : ℝ)) t Y).toReal) 1 (fun _ => false))
    ∧ (∫ Y, VectorInference.score
        (fun t Y => (twoPLPMF (fun j : Fin 2 => if j = 0 then (1 : ℝ) else 2)
          (fun _ : Fin 2 => (0 : ℝ)) t Y).toReal) 1 Y
        ∂(FisherInformation.lawOf Measure.count
          (fun t Y => (twoPLPMF (fun j : Fin 2 => if j = 0 then (1 : ℝ) else 2)
            (fun _ : Fin 2 => (0 : ℝ)) t Y).toReal) 1) = 0) := by
  have h1ne : (1 : Fin 2) ≠ 0 := by decide
  have c1 : (fun j : Fin 2 => if j = 0 then (1 : ℝ) else 2) 0
      ≠ (fun j : Fin 2 => if j = 0 then (1 : ℝ) else 2) 1 := by
    simp only [ite_true, ite_eq_right h1ne]
    norm_num
  have c2 : (∑ Y : Fin 2 → Bool, (twoPLPMF
      (fun j : Fin 2 => if j = 0 then (1 : ℝ) else 2)
      (fun _ : Fin 2 => (0 : ℝ)) 1 Y).toReal = 1) :=
    by
      have hreal : (∑' Y, twoPLPMF (fun j : Fin 2 => if j = 0 then (1 : ℝ) else 2)
          (fun _ : Fin 2 => (0 : ℝ)) 1 Y).toReal = (1 : ENNReal).toReal := by
        rw [PMF.tsum_coe]
      rw [ENNReal.tsum_toReal_eq
        (fun Y => PMF.apply_ne_top _ Y), tsum_fintype] at hreal
      simpa using hreal
  have c3 : (∀ Y : Fin 2 → Bool, 0 < (twoPLPMF
      (fun j : Fin 2 => if j = 0 then (1 : ℝ) else 2)
      (fun _ : Fin 2 => (0 : ℝ)) 1 Y).toReal) := by
    intro Y
    rw [twoPLPMF_toReal]
    apply Finset.prod_pos
    intro i _
    by_cases h : Y i = true
    · simp only [ite_eq_left h]
      exact Real.sigmoid_pos _
    · simp only [ite_eq_right h]
      exact sub_pos.mpr (Real.sigmoid_lt_one _)
  have h2t := (twoPL_score_eq_sum
    (fun j : Fin 2 => if j = 0 then (1 : ℝ) else 2)
    (fun _ : Fin 2 => (0 : ℝ)) 1) (fun _ => true)
  have h2f := (twoPL_score_eq_sum
    (fun j : Fin 2 => if j = 0 then (1 : ℝ) else 2)
    (fun _ : Fin 2 => (0 : ℝ)) 1) (fun _ => false)
  have c4 : VectorInference.score
      (fun t Y => (twoPLPMF (fun j : Fin 2 => if j = 0 then (1 : ℝ) else 2)
        (fun _ : Fin 2 => (0 : ℝ)) t Y).toReal) 1 (fun _ => true)
      ≠ VectorInference.score
        (fun t Y => (twoPLPMF (fun j : Fin 2 => if j = 0 then (1 : ℝ) else 2)
          (fun _ : Fin 2 => (0 : ℝ)) t Y).toReal) 1 (fun _ => false) := by
    rw [h2t, h2f]
    simp only [ite_true, Bool.false_eq_true, ite_false]
    have hrewrite : ∀ x z : ℝ, x * (0 - z) = x * (1 - z) - x := by
      intro x z
      ring
    simp only [hrewrite, Finset.sum_sub_distrib]
    have hA3 : (∑ j : Fin 2,
        (fun j : Fin 2 => if j = 0 then (1 : ℝ) else 2) j) = 3 := by
      simp only [Fin.sum_univ_two, ite_true, ite_eq_right h1ne]
      norm_num
    rw [hA3]
    intro hcon
    have h30 : (3 : ℝ) = 0 := by linarith
    norm_num at h30
  have c5 : (∫ Y, VectorInference.score
      (fun t Y => (twoPLPMF (fun j : Fin 2 => if j = 0 then (1 : ℝ) else 2)
        (fun _ : Fin 2 => (0 : ℝ)) t Y).toReal) 1 Y
      ∂(FisherInformation.lawOf Measure.count
        (fun t Y => (twoPLPMF (fun j : Fin 2 => if j = 0 then (1 : ℝ) else 2)
          (fun _ : Fin 2 => (0 : ℝ)) t Y).toReal) 1) = 0) :=
    integral_vector_score_twoPL (fun j : Fin 2 => if j = 0 then (1 : ℝ) else 2)
      (fun _ : Fin 2 => (0 : ℝ)) 1
  exact ⟨c1, c2, c3, c4, c5⟩

/-- Boundary: the empty item type is supported; both identities hold
with `Fin 0` items. -/
example :
    (FisherInformation.lawOf Measure.count
        (fun t Y => (twoPLPMF (fun _ : Fin 0 => (1 : ℝ)) (fun _ : Fin 0 => (0 : ℝ)) t Y).toReal) 1
      = (twoPLPMF (fun _ : Fin 0 => (1 : ℝ)) (fun _ : Fin 0 => (0 : ℝ)) 1).toMeasure)
    ∧ (∀ Y : Fin 0 → Bool,
        VectorInference.score (fun t Y => (twoPLPMF (fun _ : Fin 0 => (1 : ℝ))
          (fun _ : Fin 0 => (0 : ℝ)) t Y).toReal) 1 Y
          = ∑ j, (fun _ : Fin 0 => (1 : ℝ)) j * ((if Y j then (1 : ℝ) else 0)
              - Real.sigmoid ((fun _ : Fin 0 => (1 : ℝ)) j
                * (1 - (fun _ : Fin 0 => (0 : ℝ)) j)))) :=
  ⟨twoPL_lawOf_eq_toMeasure _ _ _, twoPL_score_eq_sum _ _ _⟩

/-- Boundary: zero and negative discriminations are supported. -/
example :
    (∫ Y, VectorInference.score (fun t Y => (twoPLPMF (fun _ : Fin 1 => (0 : ℝ))
        (fun _ : Fin 1 => (0 : ℝ)) t Y).toReal) 1 Y
      ∂(FisherInformation.lawOf Measure.count
        (fun t Y => (twoPLPMF (fun _ : Fin 1 => (0 : ℝ))
          (fun _ : Fin 1 => (0 : ℝ)) t Y).toReal) 1) = 0)
    ∧ (∫ Y, VectorInference.score (fun t Y => (twoPLPMF (fun _ : Fin 1 => (-1 : ℝ))
        (fun _ : Fin 1 => (0 : ℝ)) t Y).toReal) 1 Y
      ∂(FisherInformation.lawOf Measure.count
        (fun t Y => (twoPLPMF (fun _ : Fin 1 => (-1 : ℝ))
          (fun _ : Fin 1 => (0 : ℝ)) t Y).toReal) 1) = 0) :=
  ⟨integral_vector_score_twoPL _ _ _, integral_vector_score_twoPL _ _ _⟩

end MathlibExtTest.Probability.Statistics.Measurement.ItemScore
