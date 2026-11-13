/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.MedianTrick

open MeasureTheory ProbabilityTheory

/-- The median of a one-element family is that element. -/
example (c : ℝ) : medianOf (fun _ : Fin 1 => c) = c := by
  simp [medianOf]

/-- `medianOf` reads index `r / 2` of any sorted rearrangement of the family. -/
theorem medianOf_eq_getD_of_perm {r : ℕ} (X : Fin r → ℝ) {L : List ℝ}
    (hperm : (List.ofFn X).Perm L) (hL : L.Pairwise (· ≤ ·)) :
    medianOf X = L.getD (r / 2) 0 := by
  have hs : (Finset.univ.val.map X).sort (· ≤ ·) = L := by
    refine List.Perm.eq_of_pairwise' (Multiset.pairwise_sort _ _) hL ?_
    rw [← Multiset.coe_eq_coe, Multiset.sort_eq, Fin.univ_val_map]
    exact Multiset.coe_eq_coe.mpr hperm
  unfold medianOf
  rw [hs]

/-- An unsorted family whose first element is not the median: the values are sorted and the
middle one, at index `3 / 2 = 1`, is returned. -/
example : medianOf (![10, -3, 2] : Fin 3 → ℝ) = 2 := by
  have hofFn : List.ofFn (![10, -3, 2] : Fin 3 → ℝ) = [10, -3, 2] := by simp [List.ofFn_succ]
  have hperm : (List.ofFn (![10, -3, 2] : Fin 3 → ℝ)).Perm [-3, 2, 10] := by
    rw [hofFn]
    exact (List.Perm.swap (-3 : ℝ) 10 [2]).trans ((List.Perm.swap (2 : ℝ) 10 []).cons (-3))
  rw [medianOf_eq_getD_of_perm _ hperm (by norm_num)]
  norm_num

/-- Repeated observations are kept: the median of `0, 10, 0` is `0`. -/
example : medianOf (![0, 10, 0] : Fin 3 → ℝ) = 0 := by
  have hofFn : List.ofFn (![0, 10, 0] : Fin 3 → ℝ) = [0, 10, 0] := by simp [List.ofFn_succ]
  have hperm : (List.ofFn (![0, 10, 0] : Fin 3 → ℝ)).Perm [0, 0, 10] := by
    rw [hofFn]
    exact (List.Perm.swap (0 : ℝ) 10 []).cons 0
  rw [medianOf_eq_getD_of_perm _ hperm (by norm_num)]
  norm_num

/-- The empty family falls back to the documented default `0`. -/
example : medianOf (![] : Fin 0 → ℝ) = 0 := by
  rw [medianOf_eq_getD_of_perm _ (L := []) (by simp) (by simp)]
  rfl

/-- Boundary check `r = 1`: the median trick is the input bound amplified
to `exp (-1 / 8) > 1 / 4`. -/
example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {μ ε : ℝ} {X : Fin 1 → Ω → ℝ} (hX : iIndepFun X P) (hXm : ∀ i, Measurable (X i))
    (hbd : ∀ i, P {ω | ε < |X i ω - μ|} ≤ 1 / 4) :
    P {ω | ε < |medianOf (fun i => X i ω) - μ|} ≤
      ENNReal.ofReal (Real.exp (-(1 / 8 : ℝ))) := by
  simpa using median_trick (by decide) hX hXm hbd
