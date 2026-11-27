/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Compactification.OnePoint.ProjectiveLineThreePoints
public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic.NormNum

/-!
# Tests for moving three points of the projective line to `0`, `1` and `∞`

These examples exercise `OnePoint.exists_smul_eq_zero_one_infty` over `ℚ` and over any field,
with and without `∞` among the points, and check an explicit transformation over `ℚ`.
-/

@[expose] public section

open Matrix OnePoint

/-- Three finite points of `ℙ¹(ℚ)`. -/
example : ∃ g : GL (Fin 2) ℚ, g • ((2 : ℚ) : OnePoint ℚ) = (0 : ℚ) ∧
    g • ((5 : ℚ) : OnePoint ℚ) = (1 : ℚ) ∧ g • ((7 : ℚ) : OnePoint ℚ) = ∞ :=
  exists_smul_eq_zero_one_infty (by norm_num) (by norm_num) (by norm_num)

/-- Two finite points and `∞`, in the first position. -/
example : ∃ g : GL (Fin 2) ℚ, g • (∞ : OnePoint ℚ) = (0 : ℚ) ∧
    g • ((0 : ℚ) : OnePoint ℚ) = (1 : ℚ) ∧ g • ((1 : ℚ) : OnePoint ℚ) = ∞ :=
  exists_smul_eq_zero_one_infty (by simp) (by simp) (by norm_num)

/-- Over any field, the points `1`, `0` and `∞` in another order. -/
example (K : Type*) [Field K] [DecidableEq K] :
    ∃ g : GL (Fin 2) K, g • ((1 : K) : OnePoint K) = (0 : K) ∧
      g • ((0 : K) : OnePoint K) = (1 : K) ∧ g • (∞ : OnePoint K) = ∞ :=
  exists_smul_eq_zero_one_infty (by simp) (by simp) (by simp)

/-- The affine normalization of `2` and `5`, an explicit `z ↦ (z - 2) / 3` on `ℙ¹(ℚ)`. -/
example : (GeneralLinearGroup.mkOfDetNeZero !![1, -2; 0, 3] (by simp [det_fin_two]) :
    GL (Fin 2) ℚ) • ((5 : ℚ) : OnePoint ℚ) = (1 : ℚ) := by
  rw [smul_some_eq_ite]
  norm_num [GeneralLinearGroup.mkOfDetNeZero]
