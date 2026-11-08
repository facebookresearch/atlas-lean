/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.IharaConstantOf

@[expose] public section

open Filter
open MathlibExt.Analysis

namespace IharaConstantOfTest

/-- The zero counting sequence has abstract Ihara constant `0`. -/
example : iharaConstantOf (fun _ => 0) = 0 := by
  refine le_antisymm ?_ zero_le
  apply iharaConstantOf_le_of_eventually_le
  filter_upwards with g
  simp

/-- A constant nonzero counting sequence still has normalized limsup `0`. -/
example : iharaConstantOf (fun _ => 5) = 0 := by
  refine le_antisymm ?_ zero_le
  apply iharaConstantOf_le_of_eventually_le_add (fun _ => 5) (d := 5) (by simp)
  filter_upwards with g
  simp

/-- The identity counting sequence has abstract Ihara constant `1`. -/
example : iharaConstantOf (fun g => g) = 1 := by
  apply le_antisymm
  · apply iharaConstantOf_le_of_eventually_le
    filter_upwards with g
    simp
  · apply le_iharaConstantOf_of_frequently_le
    refine (Filter.eventually_atTop.2 ⟨1, ?_⟩).frequently
    intro g hg
    exact ⟨by omega, by simp⟩

/-- The affine counting sequence `g ↦ 2g + 3` has constant `2`. -/
example : iharaConstantOf (fun g => 2 * g + 3) = 2 := by
  apply le_antisymm
  · apply iharaConstantOf_le_of_eventually_le_add (fun g => 2 * g + 3) (d := 3) (by simp)
    filter_upwards with g
    simp
  · apply le_iharaConstantOf_of_frequently_le
    refine (Filter.eventually_atTop.2 ⟨1, ?_⟩).frequently
    intro g hg
    refine ⟨by omega, ?_⟩
    exact_mod_cast (by omega : 2 * g ≤ 2 * g + 3)

/-- A finite change at genus zero does not affect the limsup. -/
example : iharaConstantOf (fun g => if g = 0 then 100 else g) = 1 := by
  rw [iharaConstantOf_eq_of_eventually_eq
    (N := fun g => if g = 0 then 100 else g) (M := fun g => g) (G := 1) ?_]
  · apply le_antisymm
    · apply iharaConstantOf_le_of_eventually_le
      filter_upwards with g
      simp
    · apply le_iharaConstantOf_of_frequently_le
      refine (Filter.eventually_atTop.2 ⟨1, ?_⟩).frequently
      intro g hg
      exact ⟨by omega, by simp⟩
  · intro g hg
    simp [show g ≠ 0 by omega]

/-- A sequence spiking to `2g` at every even genus has constant `2`. -/
example : iharaConstantOf (fun g => if Even g then 2 * g else 0) = 2 := by
  apply le_antisymm
  · apply iharaConstantOf_le_of_eventually_le
    filter_upwards with g
    by_cases hg : Even g <;> simp [hg]
  · apply le_iharaConstantOf_of_frequently_le
    rw [Filter.frequently_atTop]
    intro a
    refine ⟨2 * (a + 1), by omega, by omega, ?_⟩
    simp

end IharaConstantOfTest
