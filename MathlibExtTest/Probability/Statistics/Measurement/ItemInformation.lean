/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Measurement.ItemInformation

/-!
# Tests for finite 2PL test information

Rasch and two-slope instances, boundary cases, ordering, and the finite
eligible-set maximum.
-/

@[expose] public section

open MeasureTheory

/-! ## instances

Executable examples: the Rasch and two-slope information values,
boundary cases, ordering, and the finite eligible-set maximum. -/

namespace MathlibExtTest.Probability.Statistics.Measurement.ItemInformation

open scoped RealInnerProductSpace
open MathlibExt.Probability.Statistics.Measurement

/-- Rasch information: one item, slope `1`, difficulty `2`, at
`θ = 2 = b`, so `p = sigmoid 0 = 1 / 2` and the information is `1 / 4`,
in both the operator and the scalar form, and it is positive. -/
example :
    (⟪MathlibExt.Probability.Statistics.VectorInference.fisherInformation
        Measure.count
        (fun t Y => (twoPLPMF (fun _ : Fin 1 => (1 : ℝ))
          (fun _ : Fin 1 => (2 : ℝ)) t Y).toReal) 2 1, (1 : ℝ)⟫ = 1 / 4)
    ∧ (MathlibExt.Probability.Statistics.FisherInformation.fisherInformation
        Measure.count
        (fun t Y => (twoPLPMF (fun _ : Fin 1 => (1 : ℝ))
          (fun _ : Fin 1 => (2 : ℝ)) t Y).toReal) 2 = 1 / 4) := by
  have h := vector_fisherInformation_twoPL (fun _ : Fin 1 => (1 : ℝ))
    (fun _ : Fin 1 => (2 : ℝ)) 2
  obtain ⟨h1, h2, _, _⟩ := h
  constructor
  · rw [h1, Fin.sum_univ_one]
    norm_num [Real.sigmoid_zero]
  · rw [← h2, h1, Fin.sum_univ_one]
    norm_num [Real.sigmoid_zero]

/-- nonidentical finite test: two items with slopes `1` and
`2` (hence nonidentical), difficulties `0`, at `θ = 0`, so each
`p j = 1 / 2` and the information is `(1 + 4) / 4 = 5 / 4`; it is
strictly positive, as the nonempty, all-slopes-positive package
requires. -/
example :
    ((fun j : Fin 2 => if j = 0 then (1 : ℝ) else 2) 0
      ≠ (fun j : Fin 2 => if j = 0 then (1 : ℝ) else 2) 1)
    ∧ (⟪MathlibExt.Probability.Statistics.VectorInference.fisherInformation
        Measure.count
        (fun t Y => (twoPLPMF (fun j : Fin 2 => if j = 0 then (1 : ℝ) else 2)
          (fun _ : Fin 2 => (0 : ℝ)) t Y).toReal) 0 1, (1 : ℝ)⟫ = 5 / 4)
    ∧ (0 < ⟪MathlibExt.Probability.Statistics.VectorInference.fisherInformation
        Measure.count
        (fun t Y => (twoPLPMF (fun j : Fin 2 => if j = 0 then (1 : ℝ) else 2)
          (fun _ : Fin 2 => (0 : ℝ)) t Y).toReal) 0 1, (1 : ℝ)⟫) := by
  have e0 : (if (0 : Fin 2) = 0 then (1 : ℝ) else 2) = 1 := by simp
  have e1 : (if (1 : Fin 2) = 0 then (1 : ℝ) else 2) = 2 :=
    ite_eq_right (by decide)
  have h := vector_fisherInformation_twoPL
    (fun j : Fin 2 => if j = 0 then (1 : ℝ) else 2) (fun _ : Fin 2 => (0 : ℝ)) 0
  obtain ⟨h1, _, _, _⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · show (if (0 : Fin 2) = 0 then (1 : ℝ) else 2)
      ≠ (if (1 : Fin 2) = 0 then (1 : ℝ) else 2)
    rw [e0, e1]
    norm_num
  · rw [h1, Fin.sum_univ_two]
    simp only [e1]
    norm_num [Real.sigmoid_zero]
  · rw [h1, Fin.sum_univ_two]
    simp only [e1]
    norm_num [Real.sigmoid_zero]

/-- empty and zero-slope boundaries: the empty test has
information `0`, and a one-item test with discrimination `0` has
information `0` at every `θ`.  These pin that no nonemptiness or slope
hypothesis is hidden in the formula, and that strict positivity really
needs a nonzero slope. -/
example :
    (⟪MathlibExt.Probability.Statistics.VectorInference.fisherInformation
        Measure.count
        (fun t Y => (twoPLPMF (fun _ : Fin 0 => (1 : ℝ))
          (fun _ : Fin 0 => (0 : ℝ)) t Y).toReal) 0 1, (1 : ℝ)⟫ = 0)
    ∧ (∀ θ : ℝ,
        ⟪MathlibExt.Probability.Statistics.VectorInference.fisherInformation
          Measure.count
          (fun t Y => (twoPLPMF (fun _ : Fin 1 => (0 : ℝ))
            (fun _ : Fin 1 => (0 : ℝ)) t Y).toReal) θ 1, (1 : ℝ)⟫ = 0) := by
  constructor
  · have h := vector_fisherInformation_twoPL (fun _ : Fin 0 => (1 : ℝ))
      (fun _ : Fin 0 => (0 : ℝ)) 0
    rw [h.1]
    simp
  · intro θ
    have h := vector_fisherInformation_twoPL (fun _ : Fin 1 => (0 : ℝ))
      (fun _ : Fin 1 => (0 : ℝ)) θ
    rw [h.1, Fin.sum_univ_one]
    simp

/-- item ordering reverses: two slope-`1` items with
difficulties `0` and `2`; item `0` carries more information at `θ = 0`
and item `1` carries more at `θ = 2`, for the per-item information
`a^2 * p * (1 - p)`. -/
example :
    ((1 : ℝ) ^ 2 * (Real.sigmoid (1 * (0 - 0)) * (1 - Real.sigmoid (1 * (0 - 0))))
      > (1 : ℝ) ^ 2 * (Real.sigmoid (1 * (0 - 2)) * (1 - Real.sigmoid (1 * (0 - 2)))))
    ∧ ((1 : ℝ) ^ 2 * (Real.sigmoid (1 * (2 - 2)) * (1 - Real.sigmoid (1 * (2 - 2))))
      > (1 : ℝ) ^ 2 * (Real.sigmoid (1 * (2 - 0)) * (1 - Real.sigmoid (1 * (2 - 0))))) := by
  constructor
  · have h0 : (1 : ℝ) * (0 - 0) = 0 := by norm_num
    have h2 : (1 : ℝ) * (0 - 2) = -2 := by norm_num
    rw [h0, h2, Real.sigmoid_zero]
    have hlt : Real.sigmoid (-2) < 1 / 2 := by
      have h := Real.sigmoid_lt (show (-2 : ℝ) < 0 by norm_num)
      simpa [Real.sigmoid_zero] using h
    have hsq : 0 < (Real.sigmoid (-2) - 1 / 2) ^ 2 :=
      sq_pos_of_ne_zero (sub_ne_zero.mpr (ne_of_lt hlt))
    nlinarith [hsq]
  · have h0 : (1 : ℝ) * (2 - 2) = 0 := by norm_num
    have h2 : (1 : ℝ) * (2 - 0) = 2 := by norm_num
    rw [h0, h2, Real.sigmoid_zero]
    have hgt : (1 : ℝ) / 2 < Real.sigmoid 2 := by
      have h := Real.sigmoid_lt (show (0 : ℝ) < 2 by norm_num)
      simpa [Real.sigmoid_zero] using h
    have hsq : 0 < (Real.sigmoid 2 - 1 / 2) ^ 2 :=
      sq_pos_of_ne_zero (sub_ne_zero.mpr (ne_of_gt hgt))
    nlinarith [hsq]

/-- eligible-set maximum: for any finite nonempty set `S` of
eligible abilities, the test information attains its maximum over `S`.
This is the existing finite-set maximum principle
(`Finset.exists_max_image`, Mathlib `Data/Finset/Max.lean`) applied to
the information function; no new maximisation principle is introduced. -/
example (a b : Fin 2 → ℝ) (S : Finset ℝ) (hS : S.Nonempty) :
    ∃ θ ∈ S, ∀ θ' ∈ S,
      ⟪MathlibExt.Probability.Statistics.VectorInference.fisherInformation
          Measure.count (fun t Y => (twoPLPMF a b t Y).toReal) θ' 1, (1 : ℝ)⟫
        ≤ ⟪MathlibExt.Probability.Statistics.VectorInference.fisherInformation
          Measure.count (fun t Y => (twoPLPMF a b t Y).toReal) θ 1, (1 : ℝ)⟫ := by
  exact Finset.exists_max_image S _ hS


/-- Direct nonnegativity: slopes `(1, 2)` on `Fin 2` at `θ = 1`,
by applying `twoPL_information_nonneg`. -/
example :
    0 ≤ ∑ j, (((fun j : Fin 2 => if j = 0 then (1 : ℝ) else 2) j) ^ 2
      * (Real.sigmoid (((fun j : Fin 2 => if j = 0 then (1 : ℝ) else 2) j)
          * (1 - (fun _ : Fin 2 => (0 : ℝ)) j))
        * (1 - Real.sigmoid (((fun j : Fin 2 => if j = 0 then (1 : ℝ) else 2) j)
          * (1 - (fun _ : Fin 2 => (0 : ℝ)) j))))) := by
  have h := twoPL_information_nonneg
    (fun j : Fin 2 => if j = 0 then (1 : ℝ) else 2) (fun _ : Fin 2 => (0 : ℝ)) 1
  exact h

/-- Direct positivity iff: slopes `(0, 2)` on `Fin 2` give strict
positivity via `twoPL_information_pos_iff`, while all-zero slopes give
information `0`. -/
example :
    (0 < ∑ j, (((fun j : Fin 2 => if j = 0 then (0 : ℝ) else 2) j) ^ 2
      * (Real.sigmoid (((fun j : Fin 2 => if j = 0 then (0 : ℝ) else 2) j)
          * (0 - (fun _ : Fin 2 => (0 : ℝ)) j))
        * (1 - Real.sigmoid (((fun j : Fin 2 => if j = 0 then (0 : ℝ) else 2) j)
          * (0 - (fun _ : Fin 2 => (0 : ℝ)) j))))))
    ∧ ((∑ j, (((fun _ : Fin 2 => (0 : ℝ)) j) ^ 2
      * (Real.sigmoid (((fun _ : Fin 2 => (0 : ℝ)) j)
          * (0 - (fun _ : Fin 2 => (0 : ℝ)) j))
        * (1 - Real.sigmoid (((fun _ : Fin 2 => (0 : ℝ)) j)
          * (0 - (fun _ : Fin 2 => (0 : ℝ)) j)))))) = 0) := by
  have e1 : (if (1 : Fin 2) = 0 then (0 : ℝ) else 2) = 2 :=
    ite_eq_right (by decide)
  have hwit : ((fun j : Fin 2 => if j = 0 then (0 : ℝ) else 2) 1) ≠ 0 := by
    simp only [e1]
    norm_num
  refine ⟨?_, ?_⟩
  · have h := (twoPL_information_pos_iff
      (fun j : Fin 2 => if j = 0 then (0 : ℝ) else 2)
      (fun _ : Fin 2 => (0 : ℝ)) 0).mpr ⟨1, hwit⟩
    exact h
  · simp
end MathlibExtTest.Probability.Statistics.Measurement.ItemInformation
