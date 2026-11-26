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

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.UniversalEnveloping.Resolution
public import MathlibExt.Algebra.Category.ModuleCat.AlgebraBarResolution
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.ResolutionComparison

/-!
# Enveloping CE and canonical bar resolution comparisons

Let L be an R-Lie algebra with free underlying module over a commutative ring. The enveloping
CE complex and the bar complex of the scalar-extension/restriction adjunction at the trivial
U_R(L)-module are projective resolutions of the same target.

Projective-resolution comparison provides maps in both directions preserving the augmentations
and homotopies from each composite to its identity. Applying any additive functor to an
abelian category preserves the homotopy equivalence and identifies the homology of the two
mapped complexes in every degree.
-/

@[expose] public section

noncomputable section

universe u v a c

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
  (L : Type v) [LieRing L] [LieAlgebra R L]

local notation "U" => UniversalEnvelopingAlgebra R L

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and T₀ = envelopingTrivialObject R L the lifted scalar U-module acted on through augmentation.
Restricting T₀ along algebraMap R U is R-linearly equivalent to ULift.{max u v} R by the
identity carrier map, since augmentation(algebraMap r) = r. -/
def envelopingTrivialGroundEquiv :
    (ModuleCat.restrictScalars (algebraMap R U)).obj (envelopingTrivialObject R L) ≃ₗ[R]
      ULift.{max u v} R :=
  { AddEquiv.refl _ with
    map_smul' := by
      intro r m
      apply ULift.ext
      change UniversalEnvelopingAlgebra.augmentation R L (algebraMap R U r) * m.down = r * m.down
      rw [(UniversalEnvelopingAlgebra.augmentation R L).commutes]
      rfl }

instance envelopingTrivial_groundFree :
    Module.Free R ((ModuleCat.restrictScalars (algebraMap R U)).obj
      (envelopingTrivialObject R L)) :=
  Module.Free.of_equiv (envelopingTrivialGroundEquiv R L).symm

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and T₀ = envelopingTrivialObject R L the lifted scalar U-module acted on through augmentation.
envelopingCanonicalBarComplex is ModuleCat.AlgebraBar.complex R U T₀, a nonnegative chain
complex of U-modules in height max u v. -/
def envelopingCanonicalBarComplex : ChainComplex (ModuleCat.{max u v} (UniversalEnvelopingAlgebra R L)) ℕ :=
  ModuleCat.AlgebraBar.complex.{u, max u v, 0} R U (envelopingTrivialObject R L)

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and T₀ = envelopingTrivialObject R L the lifted scalar U-module acted on through augmentation.
envelopingCanonicalBarAugmentation maps the canonical bar complex to single₀(T₀), using the
scalar-extension/restriction adjunction counit. -/
def envelopingCanonicalBarAugmentation :
    envelopingCanonicalBarComplex R L ⟶
      (ChainComplex.single₀ (ModuleCat.{max u v} (UniversalEnvelopingAlgebra R L))).obj
      (envelopingTrivialObject R L) :=
  ModuleCat.AlgebraBar.augmentation.{u, max u v, 0} R U (envelopingTrivialObject R L)

section FreeBase

variable [Module.Free R L]

local instance enveloping_groundFree : Module.Free R U :=
  UniversalEnvelopingAlgebra.PBW.free_of_free

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and T₀ = envelopingTrivialObject R L the lifted scalar U-module acted on through augmentation.
Assume Module.Free R L. envelopingCanonicalBarProjectiveResolution resolves T₀ with the
canonical bar complex, its counit augmentation and projective terms; PBW freeness of U and
scalar freeness of T₀ supply the required module projectivity. -/
def envelopingCanonicalBarProjectiveResolution :
    ProjectiveResolution (envelopingTrivialObject R L) :=
  ModuleCat.AlgebraBar.projectiveResolution.{u, max u v, 0} R U (envelopingTrivialObject R L)

@[simp]
theorem envelopingCanonicalBarProjectiveResolution_complex :
    (envelopingCanonicalBarProjectiveResolution R L).complex = envelopingCanonicalBarComplex R L := rfl

@[simp]
theorem envelopingCanonicalBarProjectiveResolution_π :
    (envelopingCanonicalBarProjectiveResolution R L).π = envelopingCanonicalBarAugmentation R L := rfl

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and T₀ = envelopingTrivialObject R L the lifted scalar U-module acted on through augmentation.
Assume Module.Free R L. envelopingCanonicalBarHomotopyEquiv compares envelopingComplex R L
with envelopingCanonicalBarComplex R L by projective-resolution comparison of their
augmentations to T₀. -/
def envelopingCanonicalBarHomotopyEquiv :
    HomotopyEquiv (envelopingComplex R L) (envelopingCanonicalBarComplex R L) :=
  ProjectiveResolution.homotopyEquiv (envelopingProjectiveResolution R L)
    (envelopingCanonicalBarProjectiveResolution R L)

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and T₀ = envelopingTrivialObject R L the lifted scalar U-module acted on through augmentation.
Assume Module.Free R L. envelopingToCanonicalBar is the forward map of
envelopingCanonicalBarHomotopyEquiv from the CE complex to the canonical bar complex. -/
def envelopingToCanonicalBar : envelopingComplex R L ⟶ envelopingCanonicalBarComplex R L :=
  (envelopingCanonicalBarHomotopyEquiv R L).hom

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and T₀ = envelopingTrivialObject R L the lifted scalar U-module acted on through augmentation.
Assume Module.Free R L. canonicalBarToEnveloping is the inverse comparison map from the
canonical bar complex to the enveloping CE complex. -/
def canonicalBarToEnveloping : envelopingCanonicalBarComplex R L ⟶ envelopingComplex R L :=
  (envelopingCanonicalBarHomotopyEquiv R L).inv

theorem envelopingToCanonicalBar_augmentation :
    envelopingToCanonicalBar R L ≫ envelopingCanonicalBarAugmentation R L =
      envelopingAugmentation R L :=
  ProjectiveResolution.homotopyEquiv_hom_π (envelopingProjectiveResolution R L)
    (envelopingCanonicalBarProjectiveResolution R L)

theorem canonicalBarToEnveloping_augmentation :
    canonicalBarToEnveloping R L ≫ envelopingAugmentation R L =
      envelopingCanonicalBarAugmentation R L :=
  ProjectiveResolution.homotopyEquiv_inv_π (envelopingProjectiveResolution R L)
    (envelopingCanonicalBarProjectiveResolution R L)

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and T₀ = envelopingTrivialObject R L the lifted scalar U-module acted on through augmentation.
Assume Module.Free R L. envelopingCanonicalBarHomotopy is a homotopy envelopingToCanonicalBar
≫ canonicalBarToEnveloping ∼ 𝟙(envelopingComplex R L). -/
def envelopingCanonicalBarHomotopy :
    Homotopy (envelopingToCanonicalBar R L ≫ canonicalBarToEnveloping R L)
      (𝟙 (envelopingComplex R L)) :=
  (envelopingCanonicalBarHomotopyEquiv R L).homotopyHomInvId

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and T₀ = envelopingTrivialObject R L the lifted scalar U-module acted on through augmentation.
Assume Module.Free R L. canonicalBarEnvelopingHomotopy is a homotopy canonicalBarToEnveloping
≫ envelopingToCanonicalBar ∼ 𝟙(envelopingCanonicalBarComplex R L). -/
def canonicalBarEnvelopingHomotopy :
    Homotopy (canonicalBarToEnveloping R L ≫ envelopingToCanonicalBar R L)
      (𝟙 (envelopingCanonicalBarComplex R L)) :=
  (envelopingCanonicalBarHomotopyEquiv R L).homotopyInvHomId

section Coefficients

variable {D : Type a} [Category.{c} D] [Abelian D] (F : (ModuleCat.{max u v} (UniversalEnvelopingAlgebra R L)) ⥤ D)
  [F.Additive]

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and T₀ = envelopingTrivialObject R L the lifted scalar U-module acted on through augmentation.
Assume Module.Free R L. Let D be abelian and F : ModuleCat.{max u v} U ⥤ D additive. Mapping
both complexes and homotopies along F gives a HomotopyEquiv between their F-images. -/
def envelopingCanonicalBarMappedHomotopyEquiv :
    HomotopyEquiv ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj (envelopingComplex R L))
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj (envelopingCanonicalBarComplex R L)) :=
  F.mapHomotopyEquiv (envelopingCanonicalBarHomotopyEquiv R L)

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and T₀ = envelopingTrivialObject R L the lifted scalar U-module acted on through augmentation.
Assume Module.Free R L. For an additive F : ModuleCat.{max u v} U ⥤ D into an abelian category
and n : ℕ, the resolution comparison gives H_n(F(envelopingComplex)) ≅
H_n(F(envelopingCanonicalBarComplex)). -/
def envelopingCanonicalBarHomologyIso (n : ℕ) :
    (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj (envelopingComplex R L)).homology n) ≅
      (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj (envelopingCanonicalBarComplex R L)).homology n) :=
  ProjectiveResolution.homologyComparisonIso (envelopingProjectiveResolution R L)
    (envelopingCanonicalBarProjectiveResolution R L) F n

end Coefficients
end FreeBase

end ChevalleyEilenberg
