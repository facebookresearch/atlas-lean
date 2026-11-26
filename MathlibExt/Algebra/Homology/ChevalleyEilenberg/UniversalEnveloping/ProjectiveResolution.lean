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

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.UniversalEnveloping.ProjectiveRetract
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.CategoryTheory.Abelian.LeftDerived

/-!
# Projective enveloping CE resolutions

Let L be an R-Lie algebra whose underlying module is projective over a commutative ring. Its
enveloping CE complex is exact in every positive degree, has projective U_R(L)-module terms
and augments to the trivial lifted scalar module. These data form a projective resolution.

Resolution comparison gives an augmentation-preserving homotopy equivalence with any other
projective resolution of that target. Under freeness this construction equals the free-module
resolution. Applying an additive functor to an abelian category computes its left derived
functors at the trivial module.
-/

@[expose] public section

noncomputable section

universe u v a c

open CategoryTheory CategoryTheory.Limits

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
  (L : Type v) [LieRing L] [LieAlgebra R L] [Module.Projective R L]

local notation "U" => UniversalEnvelopingAlgebra R L

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and T₀ = envelopingTrivialObject R L the lifted scalar U-module acted on through augmentation.
Assume Module.Projective R L. For every n : ℕ, envelopingComplex R L is exact at degree n + 1. -/
theorem envelopingComplex_exactAt_succ_of_projective (n : ℕ) :
    (envelopingComplex R L).ExactAt (n + 1) := by
  letI : QuasiIso (envelopingAugmentation R L) :=
    envelopingAugmentation_quasiIso_of_projective R L
  exact (quasiIsoAt_iff_exactAt' (envelopingAugmentation R L) (n + 1)
    (ChainComplex.exactAt_succ_single_obj _ _)).mp inferInstance

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and T₀ = envelopingTrivialObject R L the lifted scalar U-module acted on through augmentation.
Assume Module.Projective R L. envelopingProjectiveResolutionOfProjective resolves T₀ with
complex envelopingComplex R L, its augmentation and projective terms. -/
def envelopingProjectiveResolutionOfProjective :
    ProjectiveResolution (envelopingTrivialObject R L) where
  complex := envelopingComplex R L
  projective := fun n => inferInstance
  π := envelopingAugmentation R L
  quasiIso := envelopingAugmentation_quasiIso_of_projective R L

@[simp]
theorem envelopingProjectiveResolutionOfProjective_complex :
    (envelopingProjectiveResolutionOfProjective R L).complex =
      envelopingComplex R L := rfl

@[simp]
theorem envelopingProjectiveResolutionOfProjective_π :
    (envelopingProjectiveResolutionOfProjective R L).π =
      envelopingAugmentation R L := rfl

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and T₀ = envelopingTrivialObject R L the lifted scalar U-module acted on through augmentation.
If Module.Free R L holds, envelopingProjectiveResolutionOfProjective R L =
envelopingProjectiveResolution R L. -/
theorem envelopingProjectiveResolutionOfProjective_eq_of_free [Module.Free R L] :
    envelopingProjectiveResolutionOfProjective R L =
      envelopingProjectiveResolution R L := by
  rfl

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and T₀ = envelopingTrivialObject R L the lifted scalar U-module acted on through augmentation.
Assume Module.Projective R L. For Q : ProjectiveResolution T₀,
envelopingResolutionHomotopyEquivOfProjective gives HomotopyEquiv (envelopingComplex R L)
Q.complex by resolution comparison. -/
def envelopingResolutionHomotopyEquivOfProjective
    (Q : ProjectiveResolution (envelopingTrivialObject R L)) :
    HomotopyEquiv (envelopingComplex R L) Q.complex :=
  ProjectiveResolution.homotopyEquiv (envelopingProjectiveResolutionOfProjective R L) Q

@[reassoc (attr := simp)]
theorem envelopingResolutionHomotopyEquivOfProjective_hom_π
    (Q : ProjectiveResolution (envelopingTrivialObject R L)) :
    (envelopingResolutionHomotopyEquivOfProjective R L Q).hom ≫ Q.π =
      envelopingAugmentation R L :=
  ProjectiveResolution.homotopyEquiv_hom_π (envelopingProjectiveResolutionOfProjective R L) Q

@[reassoc (attr := simp)]
theorem envelopingResolutionHomotopyEquivOfProjective_inv_π
    (Q : ProjectiveResolution (envelopingTrivialObject R L)) :
    (envelopingResolutionHomotopyEquivOfProjective R L Q).inv ≫
        envelopingAugmentation R L = Q.π :=
  ProjectiveResolution.homotopyEquiv_inv_π (envelopingProjectiveResolutionOfProjective R L) Q

section DerivedComparison

variable {D : Type a} [Category.{c} D] [Abelian D]

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and T₀ = envelopingTrivialObject R L the lifted scalar U-module acted on through augmentation.
Assume Module.Projective R L. For an abelian D, additive F : ModuleCat.{max u v} U ⥤ D and n :
ℕ, H_n(F(envelopingComplex R L)) ≅ (F.leftDerived n).obj T₀. -/
def envelopingHomologyIsoLeftDerivedOfProjective
    (F : ModuleCat.{max u v} U ⥤ D) [F.Additive] (n : ℕ) :
    (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (envelopingComplex R L)).homology n) ≅
      (F.leftDerived n).obj (envelopingTrivialObject R L) :=
  ((envelopingProjectiveResolutionOfProjective R L).isoLeftDerivedObj F n).symm

end DerivedComparison

end ChevalleyEilenberg
