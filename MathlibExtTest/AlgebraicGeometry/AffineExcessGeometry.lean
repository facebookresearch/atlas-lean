/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.AffineExcessBetti

@[expose] public section

/-! # Tests for affine excess geometry, Betti cycle realization and the Betti
excess data -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.AffineExcessGeometry

namespace MathlibExtTest.AlgebraicGeometry.AffineExcessGeometry

variable (S : Type) [CommRing S] [Algebra ℂ S] (E : Type) [AddCommGroup E] [Module S E]

/-- The zero section is a closed immersion and a section of the projection. -/
example : IsClosedImmersion (zeroSection S E).left := inferInstance

example : zeroSection S E ≫ bundleProjection S E = 𝟙 _ := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom
      (SymmetricAlgebra.lift (0 : Module.Dual S E →ₗ[S] S)).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap S (SymmetricAlgebra S (Module.Dual S E)))) =
      𝟙 (Spec (.of S))
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext x
  exact AlgHom.commutes _ x

/-- Quotients give closed immersions. -/
example (A : Type) [CommRing A] [Algebra ℂ A] (I : Ideal A) :
    IsClosedImmersion (quotientMorphism A I).left :=
  inferInstance

/-- Extending the zero ideal gives the zero ideal. -/
example (A B : Type) [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B] [Algebra A B]
    [IsScalarTower ℂ A B] : extendedIdeal A B ⊥ = ⊥ :=
  Ideal.map_bot

/-- When the extended ideal vanishes, the whole base-changed conormal module is
excess: the excess conormal is a kernel, not a cokernel. -/
theorem excessConormal_eq_top_of_extendedIdeal_eq_bot (A B : Type) [CommRing A] [CommRing B]
    [Algebra ℂ A] [Algebra ℂ B] [Algebra A B] [IsScalarTower ℂ A B] (I : Ideal A)
    (h : extendedIdeal A B I = ⊥) : excessConormal A B I = ⊤ := by
  have hs : ∀ x : (extendedIdeal A B I).Cotangent, x = 0 := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.toCotangent_surjective _ x
    have hy : (y : B) = 0 := by
      have : (y : B) ∈ (⊥ : Ideal B) := by
        rw [← h]
        exact y.2
      exact (Submodule.mem_bot B).mp this
    have : y = 0 := Subtype.ext hy
    simp [this]
  exact LinearMap.ker_eq_top.mpr (LinearMap.ext fun z => hs _)

/-- Self-intersection: base change of `Spec (A/I) ⟶ Spec A` along itself has
the whole conormal module of `I` as excess. -/
example (A : Type) [CommRing A] [Algebra ℂ A] (I : Ideal A) :
    excessConormal A (A ⧸ I) I = ⊤ :=
  excessConormal_eq_top_of_extendedIdeal_eq_bot A (A ⧸ I) I (by
    simp [extendedIdeal, Ideal.Quotient.algebraMap_eq, Ideal.map_quotient_self])

/-- The degree cast of cycle realization is the shared Betti degree cast. -/
example : @MathlibExt.AlgebraicGeometry.BettiCycleRealization.cohomologyCast =
    @MathlibExt.AlgebraicGeometry.BettiRealization.cohomologyCast :=
  rfl

/-- A purity isomorphism makes the fundamental class an isomorphism. -/
example (Z : TopCat.{0})
    (D : MathlibExt.AlgebraicGeometry.CompactSupportBetti.DualizingComplex Z) (d : ℕ)
    (e : D.obj ≅ (MathlibExt.AlgebraicGeometry.BettiRealization.rationalUnit Z)⟦(2 * d : ℤ)⟧) :
    IsIso (MathlibExt.AlgebraicGeometry.VerdierBetti.fundamentalClass Z D d e) :=
  MathlibExt.AlgebraicGeometry.BettiCycleRealization.fundamentalClass_isIso Z D d e

end MathlibExtTest.AlgebraicGeometry.AffineExcessGeometry

end
