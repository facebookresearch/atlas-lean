/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Coordinate norm bounds from an injective finite orbit with constant coordinate squares. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- A constant-square finite orbit contributes its full size to the actual coordinate norm. -/
theorem finiteCoordinateOrbitNormBound {I J : Type*} [Fintype I] [Fintype J]
    (e : I ↪ J) (f : J → ℝ) (t : J) (hf : ∀ i, f (e i) ^ 2 = f t ^ 2) :
    (Fintype.card I : ℝ) * f t ^ 2 ≤ ∑ j, f j ^ 2 := by
  classical
  have hs : (∑ j ∈ Finset.univ.image e, f j ^ 2) =
      (Fintype.card I : ℝ) * f t ^ 2 := by
    rw [Finset.sum_image]
    · simp only [hf, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    · intro a _ b _ h
      exact e.injective h
  rw [← hs]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun i _ _ => sq_nonneg (f i))

/-- A norm upper bound applies to every coefficient repeated on an injective finite orbit. -/
theorem finiteCoordinateOrbitNormBound_of_norm {I J : Type*} [Fintype I] [Fintype J]
    (e : I ↪ J) (f : J → ℝ) (t : J) (n : ℝ)
    (hf : ∀ i, f (e i) ^ 2 = f t ^ 2) (hn : (∑ j, f j ^ 2) ≤ n) :
    (Fintype.card I : ℝ) * f t ^ 2 ≤ n :=
  (finiteCoordinateOrbitNormBound e f t hf).trans hn

/-- The same bound uses natural cardinality when the orbit has only a finiteness instance. -/
theorem finiteCoordinateOrbitNormBound_of_finite {I J : Type*} [Finite I] [Fintype J]
    (e : I ↪ J) (f : J → ℝ) (t : J) (hf : ∀ i, f (e i) ^ 2 = f t ^ 2) :
    (Nat.card I : ℝ) * f t ^ 2 ≤ ∑ j, f j ^ 2 := by
  let _ := Fintype.ofFinite I
  simpa only [Nat.card_eq_fintype_card] using finiteCoordinateOrbitNormBound e f t hf

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
