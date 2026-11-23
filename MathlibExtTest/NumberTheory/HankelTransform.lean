/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.HankelTransform

@[expose] public section

namespace MetaMathlibExt

example {R : Type*} [CommRing R] (a : ℕ → R) : hankelTransform a 0 = a 0 := by
  simp [hankelTransform]

example {R : Type*} [CommRing R] (a : ℕ → R) :
    hankelTransform a 1 = a 0 * a 2 - a 1 * a 1 := by
  simp [hankelTransform, Matrix.det_fin_two]

-- At order zero the recurrence forces the whole sequence to vanish, including its first term.
example : hankelTransform (fun _ ↦ (0 : ℤ)) 0 = 0 := by
  apply hankelTransform.eq_zero_of_recurrence _ (fun _ ↦ 1) (r := 0) le_rfl
  · exact ⟨0, le_rfl, one_ne_zero⟩
  · simp

example {K : Type*} [Ring K] (a alpha beta : ℕ → K) (mu0 : K)
    (F : ℕ → PowerSeries K) (h : HasJacobiFraction a alpha beta mu0 F) :
    PowerSeries.mk a = PowerSeries.C mu0 * F 0 :=
  h.1

example {K : Type*} [Ring K] (a alpha beta : ℕ → K) (mu0 : K)
    (F : ℕ → PowerSeries K) (h : HasJacobiFraction a alpha beta mu0 F) (i : ℕ) :
    (1 - PowerSeries.C (alpha i) * PowerSeries.X -
      PowerSeries.C (beta (i + 1)) * PowerSeries.X ^ 2 * F (i + 1)) * F i = 1 :=
  h.2 i

example {K : Type*} [Ring K] (a alpha beta : ℕ → K) (mu0 : K)
    (F : ℕ → PowerSeries K) (h : HasJacobiFraction a alpha beta mu0 F) :
    (1 - PowerSeries.C (alpha 0) * PowerSeries.X -
      PowerSeries.C (beta 1) * PowerSeries.X ^ 2 * F 1) * F 0 = 1 := by
  have := h.2 0
  simpa using this

#print axioms MetaMathlibExt.hankelTransform
#print axioms MetaMathlibExt.HasJacobiFraction

end MetaMathlibExt

end
