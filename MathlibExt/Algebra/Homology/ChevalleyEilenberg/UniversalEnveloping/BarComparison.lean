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
# Chevalley–Eilenberg and bar resolution comparison

For a Lie algebra with free underlying module over a commutative ring, the enveloping
Chevalley–Eilenberg complex and the canonical bar complex are projective resolutions of the
same trivial enveloping module.

Resolution comparison gives augmentation-preserving chain maps and a homotopy equivalence.
Every additive functor to an abelian category inherits the homotopy and homology comparisons.
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

/-- Ground restriction of the trivial enveloping algebra module recovers the lifted ground module,
by the augmentation scalar law. -/
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

/-- The canonical adjunction Bar complex of the same trivial left enveloping algebra module. -/
def envelopingCanonicalBarComplex : ChainComplex (ModuleCat.{max u v} (UniversalEnvelopingAlgebra R L)) ℕ :=
  ModuleCat.AlgebraBar.complex.{u, max u v, 0} R U (envelopingTrivialObject R L)

/-- The counit augmentation of the canonical Bar complex. -/
def envelopingCanonicalBarAugmentation :
    envelopingCanonicalBarComplex R L ⟶
      (ChainComplex.single₀ (ModuleCat.{max u v} (UniversalEnvelopingAlgebra R L))).obj
      (envelopingTrivialObject R L) :=
  ModuleCat.AlgebraBar.augmentation.{u, max u v, 0} R U (envelopingTrivialObject R L)

section FreeBase

variable [Module.Free R L]

local instance enveloping_groundFree : Module.Free R U :=
  UniversalEnvelopingAlgebra.PBW.free_of_free

/-- The canonical Bar resolution is constructed from its augmentation and terms, using the PBW and
trivial-module freeness. -/
def envelopingCanonicalBarProjectiveResolution :
    ProjectiveResolution (envelopingTrivialObject R L) :=
  ModuleCat.AlgebraBar.projectiveResolution.{u, max u v, 0} R U (envelopingTrivialObject R L)

@[simp]
theorem envelopingCanonicalBarProjectiveResolution_complex :
    (envelopingCanonicalBarProjectiveResolution R L).complex = envelopingCanonicalBarComplex R L := rfl

@[simp]
theorem envelopingCanonicalBarProjectiveResolution_π :
    (envelopingCanonicalBarProjectiveResolution R L).π = envelopingCanonicalBarAugmentation R L := rfl

/-- Comparison between the two constructed projective resolutions. -/
def envelopingCanonicalBarHomotopyEquiv :
    HomotopyEquiv (envelopingComplex R L) (envelopingCanonicalBarComplex R L) :=
  ProjectiveResolution.homotopyEquiv (envelopingProjectiveResolution R L)
    (envelopingCanonicalBarProjectiveResolution R L)

/-- The augmentation-preserving CE-to-canonical-Bar comparison. -/
def envelopingToCanonicalBar : envelopingComplex R L ⟶ envelopingCanonicalBarComplex R L :=
  (envelopingCanonicalBarHomotopyEquiv R L).hom

/-- The augmentation-preserving canonical-Bar-to-CE comparison. -/
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

/-- The CE composite is chain homotopic to its identity. -/
def envelopingCanonicalBarHomotopy :
    Homotopy (envelopingToCanonicalBar R L ≫ canonicalBarToEnveloping R L)
      (𝟙 (envelopingComplex R L)) :=
  (envelopingCanonicalBarHomotopyEquiv R L).homotopyHomInvId

/-- The canonical Bar composite is chain homotopic to its identity. -/
def canonicalBarEnvelopingHomotopy :
    Homotopy (canonicalBarToEnveloping R L ≫ envelopingToCanonicalBar R L)
      (𝟙 (envelopingCanonicalBarComplex R L)) :=
  (envelopingCanonicalBarHomotopyEquiv R L).homotopyInvHomId

section Coefficients

variable {D : Type a} [Category.{c} D] [Abelian D] (F : (ModuleCat.{max u v} (UniversalEnvelopingAlgebra R L)) ⥤ D)
  [F.Additive]

/-- Additive coefficient functors transport the comparison maps and both chain homotopies. -/
def envelopingCanonicalBarMappedHomotopyEquiv :
    HomotopyEquiv ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj (envelopingComplex R L))
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj (envelopingCanonicalBarComplex R L)) :=
  F.mapHomotopyEquiv (envelopingCanonicalBarHomotopyEquiv R L)

/-- The constructed CE and canonical Bar resolutions compute the same mapped homology for every
additive coefficient functor. -/
def envelopingCanonicalBarHomologyIso (n : ℕ) :
    (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj (envelopingComplex R L)).homology n) ≅
      (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj (envelopingCanonicalBarComplex R L)).homology n) :=
  ProjectiveResolution.homologyComparisonIso (envelopingProjectiveResolution R L)
    (envelopingCanonicalBarProjectiveResolution R L) F n

end Coefficients
end FreeBase

end ChevalleyEilenberg
