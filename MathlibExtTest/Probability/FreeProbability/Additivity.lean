/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.FreeProbability.Additivity

/-!
# Tests for additivity of free cumulants

A scalar has zero second free cumulant, and the additivity theorem applies to a scalar shift
in any unital complex algebra.
-/

open MathlibExt.Probability.FreeProbability
open MathlibExt.Probability.FreeProbabilityWanted

namespace MathlibExtTest.Probability.FreeProbability.Additivity

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- Adding a complex scalar to an element preserves its second free cumulant. -/
example (φ : A →ₗ[ℂ] ℂ) (hφ : φ 1 = 1) (a : A) (c : ℂ) :
    freeCumulant (fun k => φ ((a + algebraMap ℂ A c) ^ k)) 2 =
      freeCumulant (fun k => φ (a ^ k)) 2 := by
  have hfree : AreFree φ hφ ![a, algebraMap ℂ A c] := by
    refine isFreelyIndependent_of_eq_bot hφ _ 0 fun i hi => ?_
    have hi1 : i = 1 := by fin_cases i <;> simp_all
    subst hi1
    change Algebra.adjoin ℂ ({algebraMap ℂ A c} : Set A) = ⊥
    refine le_antisymm (Algebra.adjoin_le ?_) bot_le
    simp
  have hs (k : ℕ) : φ ((algebraMap ℂ A c) ^ k) = c ^ k := by
    rw [← map_pow, Algebra.algebraMap_eq_smul_one, map_smul, hφ, smul_eq_mul, mul_one]
  have hz : freeCumulant (fun k => φ ((algebraMap ℂ A c) ^ k)) 2 = 0 := by
    simp only [freeCumulant_two, hs, pow_one, sub_self]
  rw [freeCumulant_add_of_areFree φ hφ a _ hfree (n := 2) (hn := by decide), hz, add_zero]

end MathlibExtTest.Probability.FreeProbability.Additivity
