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
# Projective Chevalley–Eilenberg resolutions

Let `R` be a commutative ring and `L` an `R`-Lie algebra whose underlying
`R`-module is projective. The augmented Chevalley–Eilenberg complex over
`UniversalEnvelopingAlgebra R L` is a projective resolution of the trivial
enveloping module `R`.

The complex is exact in positive degrees, admits augmentation-preserving
homotopy comparisons with any projective resolution of the same module,
and computes the left derived functors of additive functors from enveloping
modules to abelian categories.
-/

@[expose] public section

noncomputable section

universe u v a c

open CategoryTheory CategoryTheory.Limits

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
  (L : Type v) [LieRing L] [LieAlgebra R L] [Module.Projective R L]

local notation "U" => UniversalEnvelopingAlgebra R L

/-- The enveloping Chevalley–Eilenberg complex is exact in each positive degree when `L` is
projective over `R`. -/
theorem envelopingComplex_exactAt_succ_of_projective (n : ℕ) :
    (envelopingComplex R L).ExactAt (n + 1) := by
  letI : QuasiIso (envelopingAugmentation R L) :=
    envelopingAugmentation_quasiIso_of_projective R L
  exact (quasiIsoAt_iff_exactAt' (envelopingAugmentation R L) (n + 1)
    (ChainComplex.exactAt_succ_single_obj _ _)).mp inferInstance

/-- The Chevalley–Eilenberg projective resolution of the trivial enveloping module when `L` is
projective over `R`. -/
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

/-- For a free Lie carrier, the projective construction agrees with the free construction. -/
theorem envelopingProjectiveResolutionOfProjective_eq_of_free [Module.Free R L] :
    envelopingProjectiveResolutionOfProjective R L =
      envelopingProjectiveResolution R L := by
  rfl

/-- An augmentation-preserving homotopy equivalence with any projective resolution of the trivial
enveloping module. -/
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

/-- Applying an additive functor to the Chevalley–Eilenberg resolution computes its left derived
functors on the trivial enveloping module. -/
def envelopingHomologyIsoLeftDerivedOfProjective
    (F : ModuleCat.{max u v} U ⥤ D) [F.Additive] (n : ℕ) :
    (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (envelopingComplex R L)).homology n) ≅
      (F.leftDerived n).obj (envelopingTrivialObject R L) :=
  ((envelopingProjectiveResolutionOfProjective R L).isoLeftDerivedObj F n).symm

end DerivedComparison

end ChevalleyEilenberg
