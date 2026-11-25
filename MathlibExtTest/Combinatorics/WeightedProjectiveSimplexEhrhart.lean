/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.WeightedProjectiveSimplexEhrhart
import Mathlib.RingTheory.PowerSeries.WellKnown

/-! # Ehrhart series of a point and polynomial unimodality -/

open MetaMathlibExt

-- The unique point in dimension zero contributes to every dilate, including at zero.
private theorem ehrhart_point (t : ℕ) : ehrhart (Set.univ : Set (Fin 0 → ℝ)) t = 1 := by
  have h (x : Fin 0 → ℤ) :
      IsLatticePoint (polytopeDilate t (Set.univ : Set (Fin 0 → ℝ))) x :=
    ⟨0, Set.mem_univ _, Subsingleton.elim ..⟩
  simp [ehrhart, h]

example : IsHStarPolynomial (Set.univ : Set (Fin 0 → ℝ)) 1 := by
  simp only [IsHStarPolynomial, ehrhart_point, Fintype.card_fin, zero_add, Nat.cast_one,
    Polynomial.coe_one]
  rw [← PowerSeries.invOneSubPow_inv_eq_one_sub_pow ℤ 1]
  convert (PowerSeries.invOneSubPow ℤ 1).val_inv using 2
  ext n
  simp [PowerSeries.invOneSubPow]

-- The zero polynomial has a peak at zero.
example : IsUnimodal 0 := by
  exact ⟨0, by simp, by simp, by simp⟩
