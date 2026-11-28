/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.ChainGradedPairingFirstPositiveImages

/-!
# Right degree-zero components in first-positive pairing images

Let R be a ring and choose a monoidal preadditive structure on its
module category. For a chain graded pairing P, the first-positive
degree n image sums p>0 and q≥0 with p+q=n.
It therefore includes the (n,0) component whenever n>0.

If that component is surjective, the entire image is K₃,n.
With d₁:K₁,1→K₁,0 equal to zero so the first-positive chain pairing
is defined, its degree n cokernel is then a zero object.
The scalar and module carrier universes are independent.
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

/-- Let R be a ring in universe u and ModuleCat_v R have a chosen
monoidal preadditive structure. Let P be a chain graded pairing
K₁⊗K₂→K₃ of nonnegative module complexes.
Write I_n for the sum of ranges with p>0,q≥0,p+q=n.
For n>0, range(P_(n,0))≤I_n. The right bidegree is zero,
and this component is part of the first-positive family. -/
theorem range_pair_right_zero_le_firstPositiveImages (n : ℕ) (hn : 0 < n) :
    LinearMap.range (pairAt P n 0 n (Nat.add_zero n)).hom ≤ firstPositiveImages P n := by
  rintro y ⟨x, rfl⟩
  exact pairAt_mem_firstPositiveImages P n 0 n (Nat.add_zero n) hn x

/-- Let R be a ring in universe u and ModuleCat_v R have a chosen
monoidal preadditive structure. Let P be a chain graded pairing
K₁⊗K₂→K₃ of nonnegative module complexes.
Write I_n for the sum of ranges with p>0,q≥0,p+q=n.
For n>0, if P_(n,0) is surjective then I_n=K₃,n. -/
theorem firstPositiveImages_eq_top_of_right_zero_surjective (n : ℕ) (hn : 0 < n)
    (h : Function.Surjective (pairAt P n 0 n (Nat.add_zero n)).hom) :
    firstPositiveImages P n = ⊤ := by
  apply top_unique
  intro y _
  obtain ⟨x, rfl⟩ := h y
  exact range_pair_right_zero_le_firstPositiveImages P n hn ⟨x, rfl⟩

/-- Let R be a ring in universe u and ModuleCat_v R have a chosen
monoidal preadditive structure. Let P be a chain graded pairing
K₁⊗K₂→K₃ of nonnegative module complexes.
Write I_n for the sum of ranges with p>0,q≥0,p+q=n.
If K₁.d(1,0)=0, n>0 and P_(n,0) is surjective, then the
degree n term of the first-positive pairing cokernel is a zero object. -/
theorem firstPositiveCokernel_X_isZero_of_right_zero_surjective
    (h₁ : K₁.d 1 0 = 0) (n : ℕ) (hn : 0 < n)
    (h : Function.Surjective (pairAt P n 0 n (Nat.add_zero n)).hom) :
    IsZero ((firstPositiveCokernel P h₁).X n) := by
  have hz : IsZero (firstPositiveDegreeQuotient P n) := by
    apply ModuleCat.isZero_iff_subsingleton.mpr
    change Subsingleton ((K₃.X n) ⧸ firstPositiveImages P n)
    rw [firstPositiveImages_eq_top_of_right_zero_surjective P n hn h]
    infer_instance
  exact hz.of_iso (firstPositiveCokernelDegreeIso P h₁ n)

end HomologicalComplex.ChainGradedPairing
