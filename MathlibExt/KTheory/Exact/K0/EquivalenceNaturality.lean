/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.KTheory.Exact.K0.Equivalence

/-!
# Naturality of exact-category K₀ ring equivalences

An ordinary natural isomorphism between the actual functor factorizations
induces a commuting square of the canonical `K₀` ring maps. The same square
commutes in the inverse comparison direction, using the original inverse
functions and requiring monoidal structures only on the forward equivalence
functors.
-/

@[expose] public section

open CategoryTheory Limits

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

namespace AlgebraicKTheory

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C]
  [ExactCategory.IsTensorBiexact C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
  [MonoidalCategory D] [BraidedCategory D] [MonoidalPreadditive D]
  [ExactCategory.IsTensorBiexact D]
variable {C' : Type u₃} [Category.{v₃} C'] [Preadditive C']
  [HasZeroObject C'] [HasBinaryBiproducts C'] [ExactCategory C']
  [MonoidalCategory C'] [BraidedCategory C'] [MonoidalPreadditive C']
  [ExactCategory.IsTensorBiexact C']
variable {D' : Type u₄} [Category.{v₄} D'] [Preadditive D']
  [HasZeroObject D'] [HasBinaryBiproducts D'] [ExactCategory D']
  [MonoidalCategory D'] [BraidedCategory D'] [MonoidalPreadditive D']
  [ExactCategory.IsTensorBiexact D']

variable (e : C ≌ D) (e' : C' ≌ D')
  [e.functor.Additive] [e.inverse.Additive] [e.functor.IsExact] [e.inverse.IsExact]
  [e.functor.Monoidal]
  [e'.functor.Additive] [e'.inverse.Additive] [e'.functor.IsExact] [e'.inverse.IsExact]
  [e'.functor.Monoidal]
variable (F : C ⥤ C') (G : D ⥤ D')
  [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] [F.Monoidal] [G.Monoidal]

/-- A natural isomorphism of the actual functor factorizations gives equality
of the whole forward `K₀` ring maps. -/
theorem K0.ringEquivOfEquivalence_naturality
    (n : F ⋙ e'.functor ≅ e.functor ⋙ G) :
    (K0.ringEquivOfEquivalence e' : K0 C' →+* K0 D').comp (K0.mapRing F) =
      (K0.mapRing G).comp (K0.ringEquivOfEquivalence e : K0 C →+* K0 D) := by
  rw [K0.ringEquivOfEquivalence_toRingHom, K0.ringEquivOfEquivalence_toRingHom]
  rw [← K0.mapRing_comp F e'.functor, ← K0.mapRing_comp e.functor G]
  exact K0.mapRing_eq_of_iso n

/-- The natural square commutes for the whole inverse comparison maps, using
only the monoidal structures on the forward equivalence functors. -/
theorem K0.ringEquivOfEquivalence_symm_naturality
    (n : F ⋙ e'.functor ≅ e.functor ⋙ G) :
    ((K0.ringEquivOfEquivalence e').symm : K0 D' →+* K0 C').comp (K0.mapRing G) =
      (K0.mapRing F).comp ((K0.ringEquivOfEquivalence e).symm : K0 D →+* K0 C) := by
  ext x
  apply (K0.ringEquivOfEquivalence e').injective
  change K0.ringEquivOfEquivalence e'
      ((K0.ringEquivOfEquivalence e').symm (K0.mapRing G x)) =
    K0.ringEquivOfEquivalence e'
      (K0.mapRing F ((K0.ringEquivOfEquivalence e).symm x))
  rw [RingEquiv.apply_symm_apply]
  have hn := DFunLike.congr_fun (K0.ringEquivOfEquivalence_naturality e e' F G n)
    ((K0.ringEquivOfEquivalence e).symm x)
  change K0.ringEquivOfEquivalence e'
      (K0.mapRing F ((K0.ringEquivOfEquivalence e).symm x)) =
    K0.mapRing G (K0.ringEquivOfEquivalence e ((K0.ringEquivOfEquivalence e).symm x)) at hn
  rw [RingEquiv.apply_symm_apply] at hn
  exact hn.symm

end AlgebraicKTheory
