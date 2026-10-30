/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Approximation.Equioscillation

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tests for Chebyshev equioscillation and de la Vallée Poussin

* `x ↦ x ^ 2` on `[-1, 1]`: the constant `1 / 2` is the unique best uniform
  approximation among polynomials of degree at most `1`, with error `1 / 2`,
  equioscillating at `-1, 0, 1`.
* `x ↦ x ^ 3` on `[-1, 1]`: `(3 / 4) • x` is the unique best uniform
  approximation among polynomials of degree at most `2`, with error `1 / 4`,
  equioscillating at `-1, -1 / 2, 1 / 2, 1` (the Chebyshev polynomial `T₃` case).
* `x ↦ x ^ 2` on `[0, 1]`: the constant `1 / 2` is the unique best uniform
  approximation among constants, with error `1 / 2`, equioscillating at `0, 1`.
* De la Vallée Poussin: the constant `1 / 4` for `x ↦ x ^ 2` on `[-1, 1]` has
  alternating error at `-1, 0, 1` bounded below by `1 / 4`, so no polynomial of
  degree at most `1` has uniform error `< 1 / 4` there.
* `#print axioms` for the main theorems: standard triple only.
-/

namespace MathlibExtTest.Analysis.Approximation.EquioscillationTests

open Polynomial
open MathlibExt.Analysis.Approximation.Equioscillation

/-- The equioscillation points `-1, 0, 1` for `x ↦ x ^ 2` on `[-1, 1]`. -/
def ptsSq : ℕ → ℝ := fun k => if k = 0 then -1 else if k = 1 then 0 else 1

/-- The equioscillation points `-1, -1 / 2, 1 / 2, 1` for `x ↦ x ^ 3` on `[-1, 1]`. -/
noncomputable def ptsCube : ℕ → ℝ :=
  fun k => if k = 0 then -1 else if k = 1 then -1 / 2 else if k = 2 then 1 / 2 else 1

/-- The equioscillation points `0, 1` for `x ↦ x ^ 2` on `[0, 1]`. -/
def pts01 : ℕ → ℝ := fun k => if k = 0 then 0 else 1

/-- The error of the constant `1 / 2` against `x ↦ x ^ 2` equioscillates at
`-1, 0, 1` with amplitude `1 / 2` and sign `1`. -/
theorem equioscillates_sq :
    Equioscillates (fun y => y ^ 2) (-1) 1 1 (C (1 / 2 : ℝ)) (1 / 2) 1 ptsSq := by
  refine ⟨Or.inl rfl, ?_, ?_, ?_, ?_⟩
  · simp [natDegree_C]
  · intro i hi j hj hij
    obtain ⟨h0i, h2i⟩ := hi
    obtain ⟨h0j, h2j⟩ := hj
    rcases (by omega : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2)) with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [ptsSq]
  · intro i hi
    obtain ⟨h0i, h2i⟩ := hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> simp [ptsSq]
  · intro i hi
    obtain ⟨h0i, h2i⟩ := hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> simp [ptsSq] <;>
      norm_num

/-- The constant `1 / 2` is the unique polynomial of degree at most `1` whose
uniform error against `x ↦ x ^ 2` on `[-1, 1]` is at most `1 / 2`. -/
theorem sq_best_const {q : ℝ[X]} (hq : q.natDegree ≤ 1)
    (herr : ∀ y ∈ Set.Icc (-1 : ℝ) 1, |(fun y => y ^ 2) y - q.eval y| ≤ 1 / 2) :
    q = C (1 / 2 : ℝ) :=
  eq_of_equioscillates equioscillates_sq hq herr

/-- No polynomial of degree at most `1` has uniform error against `x ↦ x ^ 2`
on `[-1, 1]` strictly less than `1 / 2`. -/
theorem sq_no_better {q : ℝ[X]} (hq : q.natDegree ≤ 1) :
    ¬ ∀ y ∈ Set.Icc (-1 : ℝ) 1, |(fun y => y ^ 2) y - q.eval y| < 1 / 2 :=
  not_lt_of_equioscillates equioscillates_sq hq

/-- The error of `(3 / 4) • x` against `x ↦ x ^ 3` equioscillates at
`-1, -1 / 2, 1 / 2, 1` with amplitude `1 / 4` and sign `-1`. -/
theorem equioscillates_cube :
    Equioscillates (fun y => y ^ 3) (-1) 1 2 (C (3 / 4 : ℝ) * X) (1 / 4) (-1) ptsCube := by
  refine ⟨Or.inr rfl, ?_, ?_, ?_, ?_⟩
  · have h := natDegree_mul_le (p := C (3 / 4 : ℝ)) (q := (X : ℝ[X]))
    rw [natDegree_C, natDegree_X] at h
    omega
  · intro i hi j hj hij
    obtain ⟨h0i, h3i⟩ := hi
    obtain ⟨h0j, h3j⟩ := hj
    rcases (by omega : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨
      (i = 1 ∧ j = 2) ∨ (i = 1 ∧ j = 3) ∨ (i = 2 ∧ j = 3)) with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [ptsCube] <;> norm_num
  · intro i hi
    obtain ⟨h0i, h3i⟩ := hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
      simp [ptsCube] <;> norm_num
  · intro i hi
    obtain ⟨h0i, h3i⟩ := hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
      simp [ptsCube] <;> norm_num

/-- `(3 / 4) • x` is the unique polynomial of degree at most `2` whose uniform
error against `x ↦ x ^ 3` on `[-1, 1]` is at most `1 / 4`. -/
theorem cube_best_quad {q : ℝ[X]} (hq : q.natDegree ≤ 2)
    (herr : ∀ y ∈ Set.Icc (-1 : ℝ) 1, |(fun y => y ^ 3) y - q.eval y| ≤ 1 / 4) :
    q = C (3 / 4 : ℝ) * X :=
  eq_of_equioscillates equioscillates_cube hq herr

/-- The error of the constant `1 / 2` against `x ↦ x ^ 2` equioscillates at
`0, 1` with amplitude `1 / 2` and sign `-1`. -/
theorem equioscillates_sq01 :
    Equioscillates (fun y => y ^ 2) 0 1 0 (C (1 / 2 : ℝ)) (1 / 2) (-1) pts01 := by
  refine ⟨Or.inr rfl, ?_, ?_, ?_, ?_⟩
  · simp [natDegree_C]
  · intro i hi j hj hij
    obtain ⟨h0i, h1i⟩ := hi
    obtain ⟨h0j, h1j⟩ := hj
    rcases (by omega : i = 0 ∧ j = 1) with ⟨rfl, rfl⟩
    simp [pts01]
  · intro i hi
    obtain ⟨h0i, h1i⟩ := hi
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> simp [pts01]
  · intro i hi
    obtain ⟨h0i, h1i⟩ := hi
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> simp [pts01]
    norm_num

/-- The constant `1 / 2` is the unique constant whose uniform error against
`x ↦ x ^ 2` on `[0, 1]` is at most `1 / 2`. -/
theorem sq01_best_const {q : ℝ[X]} (hq : q.natDegree ≤ 0)
    (herr : ∀ y ∈ Set.Icc (0 : ℝ) 1, |(fun y => y ^ 2) y - q.eval y| ≤ 1 / 2) :
    q = C (1 / 2 : ℝ) :=
  eq_of_equioscillates equioscillates_sq01 hq herr

/-- De la Vallée Poussin applied to `x ↦ x ^ 2` on `[-1, 1]` with the
constant `1 / 4`: no polynomial of degree at most `1` has uniform error
strictly less than `1 / 4` there. -/
theorem dvp_sq_lower_bound {q : ℝ[X]} (hq : q.natDegree ≤ 1) :
    ¬ ∀ y ∈ Set.Icc (-1 : ℝ) 1, |(fun y => y ^ 2) y - q.eval y| < 1 / 4 := by
  apply de_la_vallee_poussin (σ := (1 : ℝ)) (η := 1 / 4)
    (p := C (1 / 4 : ℝ)) (x := ptsSq) (f := fun y => y ^ 2) (a := -1) (b := 1) (n := 1)
  · left
    rfl
  · simp [natDegree_C]
  · intro i hi j hj hij
    obtain ⟨h0i, h2i⟩ := hi
    obtain ⟨h0j, h2j⟩ := hj
    rcases (by omega : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2)) with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [ptsSq]
  · intro i hi
    obtain ⟨h0i, h2i⟩ := hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> simp [ptsSq]
  · intro i hi
    obtain ⟨h0i, h2i⟩ := hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> simp [ptsSq] <;>
      norm_num
  · exact hq

#print axioms MathlibExt.Analysis.Approximation.Equioscillation.eq_of_equioscillates
#print axioms MathlibExt.Analysis.Approximation.Equioscillation.not_lt_of_equioscillates
#print axioms MathlibExt.Analysis.Approximation.Equioscillation.de_la_vallee_poussin

end MathlibExtTest.Analysis.Approximation.EquioscillationTests
