/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.ChainGradedPairingFirstPositiveImages

/-!
# Degree-zero right factors in the actual first-positive image family

The existing first-positive family includes (n,0) whenever n is positive.
Consequently, a surjective actual right-degree-zero component makes that
entire degree's image family top. This is a fact about the existing native
image definition; it makes no identification with a book's ideal convention.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

universe u v

namespace HomologicalComplex.ChainGradedPairing

variable {R : Type u} [Ring R]
  [MonoidalCategory (ModuleCat.{v} R)] [MonoidalPreadditive (ModuleCat.{v} R)]
  {K₁ K₂ K₃ : ChainComplex (ModuleCat.{v} R) ℕ}
  (P : ChainGradedPairing K₁ K₂ K₃)

/-- The actual (n,0) image is included when n is positive. -/
theorem range_pair_right_zero_le_firstPositiveImages (n : ℕ) (hn : 0 < n) :
    LinearMap.range (pairAt P n 0 n (Nat.add_zero n)).hom ≤ firstPositiveImages P n := by
  rintro y ⟨x, rfl⟩
  exact pairAt_mem_firstPositiveImages P n 0 n (Nat.add_zero n) hn x

/-- Surjectivity of an actual (n,0) component fills the original first-positive image degree. -/
theorem firstPositiveImages_eq_top_of_right_zero_surjective (n : ℕ) (hn : 0 < n)
    (h : Function.Surjective (pairAt P n 0 n (Nat.add_zero n)).hom) : firstPositiveImages P n = ⊤ := by
  apply top_unique
  intro y _
  obtain ⟨x, rfl⟩ := h y
  exact range_pair_right_zero_le_firstPositiveImages P n hn ⟨x, rfl⟩

/-- The actual first-positive cokernel component is zero when the original (n,0) component is surjective. -/
theorem firstPositiveCokernel_X_isZero_of_right_zero_surjective
    (h₁ : K₁.d 1 0 = 0) (n : ℕ) (hn : 0 < n)
    (h : Function.Surjective (pairAt P n 0 n (Nat.add_zero n)).hom) : IsZero ((firstPositiveCokernel P h₁).X n) := by
  have hz : IsZero (firstPositiveDegreeQuotient P n) := by
    apply ModuleCat.isZero_iff_subsingleton.mpr
    change Subsingleton ((K₃.X n) ⧸ firstPositiveImages P n)
    rw [firstPositiveImages_eq_top_of_right_zero_surjective P n hn h]
    infer_instance
  exact hz.of_iso (firstPositiveCokernelDegreeIso P h₁ n)

end HomologicalComplex.ChainGradedPairing
