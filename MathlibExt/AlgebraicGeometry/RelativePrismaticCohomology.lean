/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import MathlibExt.AlgebraicGeometry.RelativePrismaticSite
public import MathlibExt.RingTheory.DerivedModuleScalarOperations

/-!
# Actual relative prismatic derived sections and scalar specializations

Derived sections are the right Kan-derived functor of the actual limit
of the structural module diagram. The existence input names this fixed
source. Specialization is completed derived scalar extension along the
actual quotient map composed with the actual prism Frobenius.

Generic derived-existence and completion inputs are source integration,
separate from prismatic comparison theorems. This completed definition
does not assert a geometric de Rham or Hodge--Tate comparison.

Reference: Bhatt--Scholze, arXiv:1905.08229v4, Theorem 1.8.
The Kan constructions are native Mathlib, and the completed scalar
operations retain their source notices.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RelativePrismaticCohomology

open CategoryTheory CategoryTheory.Limits
open MathlibExt.RingTheory MathlibExt.RingTheory.BoundedPrisms
open MathlibExt.RingTheory.DerivedModuleScalarOperations
open MathlibExt.AlgebraicGeometry.PadicFormalSchemes
open RelativePrismaticSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (p : ℕ) [Fact p.Prime] (P : Prism.{u} p)
  (X : FormalScheme p P.ring P.ideal)

abbrev Coefficients := ModuleCat.{u + 1} P.ring
abbrev Sheaves := Sheaf (topology p P X) (Coefficients p P)

instance coefficientsSiteLimits :
    HasLimitsOfShape (Obj p P X)ᵒᵖ (Coefficients p P) := by
  let : HasLimitsOfSize.{u, u + 1} (Coefficients p P) :=
    ModuleCat.hasLimitsOfSize.{u, u + 1, u + 1, u}
  infer_instance

/-- Actual sections of a sheaf are the limit of its module presheaf. -/
def sections : Sheaves p P X ⥤ Coefficients p P :=
  sheafToPresheaf (topology p P X) _ ⋙ lim.{u, u + 1, u + 1, u + 2}

instance sections_additive : (sections p P X).Additive where
  map_add {F G} f g := by
    apply limit.hom_ext
    intro U
    change limMap (f.hom + g.hom) ≫ limit.π G.obj U =
      (limMap f.hom + limMap g.hom) ≫ limit.π G.obj U
    rw [Preadditive.add_comp]
    simp

/-- The actual degreewise-sections source into module derived objects. -/
def sectionsSource : CochainComplex (Sheaves p P X) ℤ ⥤
    DerivedCategory (Coefficients p P) :=
  (sections p P X).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    DerivedCategory.Q

abbrev sheafQuasiIso :
    MorphismProperty (CochainComplex (Sheaves p P X) ℤ) :=
  HomologicalComplex.quasiIso (Sheaves p P X) (ComplexShape.up ℤ)

/-- Generic right-derived existence for this fixed actual sections source. -/
class HasDerivedSections : Prop where
  exists_derived : (sectionsSource p P X).HasRightDerivedFunctor
    (sheafQuasiIso p P X)

attribute [instance] HasDerivedSections.exists_derived

variable [HasDerivedSections p P X]

/-- The actual derived-sections functor, selected by its Kan property. -/
def derivedSections : DerivedCategory (Sheaves p P X) ⥤
    DerivedCategory (Coefficients p P) :=
  (sectionsSource p P X).totalRightDerived DerivedCategory.Q
    (sheafQuasiIso p P X)

/-- Its canonical comparison from the actual degreewise source. -/
def derivedSectionsUnit : sectionsSource p P X ⟶
    DerivedCategory.Q ⋙ derivedSections p P X :=
  (sectionsSource p P X).totalRightDerivedUnit DerivedCategory.Q
    (sheafQuasiIso p P X)

instance derivedSections_isRightDerived :
    (derivedSections p P X).IsRightDerivedFunctor
      (derivedSectionsUnit p P X) (sheafQuasiIso p P X) := by
  dsimp only [derivedSections, derivedSectionsUnit]
  infer_instance

/-- R-Gamma of the actual structural prism-module sheaf. -/
def prismatic : DerivedCategory (Coefficients p P) :=
  (derivedSections p P X).obj
    ((DerivedCategory.singleFunctor (Sheaves p P X) 0).obj
      (structureSheaf p P X))

/-- The actual Frobenius-restricted structural presheaf, sheafified. -/
def frobeniusStructureSheaf : Sheaves p P X :=
  (presheafToSheaf (topology p P X) _).obj
    (structurePresheaf p P X ⋙
      ModuleCat.restrictScalars (DeltaRing.frobenius p P.ring))

/-- Sheafification of the actual semilinear delta-Frobenius. -/
def frobeniusSheaf : structureSheaf p P X ⟶
    frobeniusStructureSheaf p P X :=
  (presheafToSheaf (topology p P X) _).map
    (frobeniusPresheaf p P X)

/-- R-Gamma applied to that actual coefficient-Frobenius map. Its target
is the computed sheafified restriction, not a freely chosen endomorphism. -/
def frobenius : prismatic p P X ⟶
    (derivedSections p P X).obj
      ((DerivedCategory.singleFunctor (Sheaves p P X) 0).obj
        (frobeniusStructureSheaf p P X)) :=
  (derivedSections p P X).map
    ((DerivedCategory.singleFunctor (Sheaves p P X) 0).map
      (frobeniusSheaf p P X))

/-- The actual coefficient map for the de Rham comparison. -/
def deRhamScalars : P.ring →+* P.Residue :=
  (Ideal.Quotient.mk P.ideal).comp (DeltaRing.frobenius p P.ring)

/-- Completed derived specialization along phi_A followed by A→A/I. -/
def deRhamSpecialization [HasExtension (deRhamScalars p P)]
    (C : Completion P.Residue (Ideal.span {(p : P.Residue)})) :
    DerivedCategory (ModuleCat.{u + 1} P.Residue) :=
  (completedExtension (deRhamScalars p P) C).obj (prismatic p P X)

end MathlibExt.AlgebraicGeometry.RelativePrismaticCohomology
