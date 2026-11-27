/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Hypercontractivity.BonamiLemma
import Mathlib.Tactic.NormNum

open BooleanCube
open scoped BigOperators

/-! ### The (2,4)-Hypercontractivity Theorem and the Bonami Lemma -/

/-- (2,4)-hypercontractivity for an arbitrary function on the 4-cube. -/
example (f : BoolCube 4 → ℝ) :
    𝔼 x, boolNoiseOp (Real.sqrt (1 / 3)) f x ^ 4 ≤ (𝔼 x, f x ^ 2) ^ 2 :=
  expect_boolNoiseOp_pow_four_le f

/-- The Bonami Lemma for a character: `χ_S` has degree `|S|`, and `𝔼[χ_S⁴] = 1 ≤ 9^|S|`. -/
example (S : Finset (Fin 3)) :
    𝔼 x, cubeChi 3 S x ^ 4 ≤ 9 ^ S.card * (𝔼 x, cubeChi 3 S x ^ 2) ^ 2 := by
  refine bonami_lemma _ fun T hT => ?_
  have hne : T ≠ S := by
    rintro rfl
    exact lt_irrefl _ hT
  simp [boolFourierCoeff_cubeChi, Ne.symm hne]

/-- At degree `0` (constants) the Bonami Lemma is an equality: `c⁴ ≤ 1 · (c²)²`. -/
example (c : ℝ) : 𝔼 _x : BoolCube 2, c ^ 4 ≤ 9 ^ 0 * (𝔼 _x : BoolCube 2, c ^ 2) ^ 2 := by
  refine bonami_lemma (fun _ => c) fun T hT => ?_
  have hne : T ≠ ∅ := Finset.nonempty_iff_ne_empty.mp (Finset.card_pos.mp hT)
  simp [boolFourierCoeff_const, hne]

/-- The Bonami Lemma at degree one, for any function of degree at most one. -/
example (f : BoolCube 5 → ℝ) (hf : MultilinearDegreeLE 5 f 1) :
    𝔼 x, f x ^ 4 ≤ 9 * (𝔼 x, f x ^ 2) ^ 2 := by
  simpa using bonami_lemma f hf
